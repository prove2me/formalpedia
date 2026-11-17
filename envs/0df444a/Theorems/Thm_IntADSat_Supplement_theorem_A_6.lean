-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_A_6
-- name    : IntADSat.Supplement.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:55:56.470201+00:00
-- url     : https://prove2.me/theorems/4403bdc2-ed16-4a26-85e1-57b8c8f9d640
-- title:
--   Theorem A.6 — finite integral closure: $\Lambda_G=\Lambda_{r-1+\lfloor\log_2 I_0\rfloor}$, $I_0\le r^{r/2}\Delta_*^{r(r-1)/2}$, polynomial-time basis and Smith invariants
-- statement:
--   Let $G$ be a graph on $n\ge1$ vertices, $r=r_G=\dim_{\mathbb Q}M_{\mathbb Q}(G)$, $\Lambda_t$ the integer span of the word vectors $w(A,D)e$ with $|w|\le t$, $\Delta_*=\max(1,\max_v\deg v)$, and
--   $$I_0=\big[M_{\mathbb Q}(G)\cap\mathbb Z^n:\Lambda_{r-1}\big].$$
--   Then $I_0$ is finite and
--   $$\Lambda_G=\Lambda_{r-1+\lfloor\log_2 I_0\rfloor},\qquad I_0\le r^{r/2}\,\Delta_*^{r(r-1)/2}.$$
--   In particular, all word vectors of length at most
--   $$L=r-1+\Big\lceil\frac r2\log_2 r+\frac{r(r-1)}2\log_2\Delta_*\Big\rceil\tag{A.1}$$
--   generate $\Lambda_G$. Moreover, a lattice basis of $\Lambda_G$ and its Smith invariants can be computed in deterministic polynomial time in the graph order: there is a single deterministic Turing machine that, on the $n^2$-bit adjacency code of any graph $G$ with $n\ge1$ vertices, outputs in time polynomial in $n$ the binary code of a $\mathbb Z$-basis of $\Lambda_G$ together with the Smith invariants $s_1\mid\cdots\mid s_r$ of $\Lambda_G\subseteq\mathbb Z^n$.
--
--   The theorem makes the integral closure of the word filtration effective: it bounds the word length needed to generate $\Lambda_G$ and makes the defect group $\mathbb Z^n/\Lambda_G$ exactly computable.
--
--   **Formalization Note** The machine is Mathlib's multi-stack Turing machine (`Turing.TM2ComputableInPolyTime`) on binary strings, with time polynomial in the input length $n^2$; polynomial bit complexity does not depend on the machine model. Numbers in the output are in self-delimiting binary.
--
--   Differences from the source:
--   - encoding: graphs have at least one vertex → hypothesis 0 < n; reason: standing assumption of the paper (p.11)
--   - encoding: I_0 = [M_ℚ(G) ∩ ℤⁿ : Λ_{r−1}] is finite → I₀ = relIndex of Λ_{r−1} in the pull-back of M_ℚ(G) to ℤⁿ, and 0 < I₀; reason: relIndex is 0 exactly for infinite index
--   - encoding: ⌊log₂ I_0⌋; r^{r/2}, Δ_*^{r(r−1)/2}; log₂ → Nat.log 2 I₀; real powers; Real.logb 2; reason: same values for I₀ ≥ 1, r ≥ 1, Δ_* ≥ 1
--   - reading: a lattice basis and its Smith invariants can be computed in deterministic polynomial time in the graph order → one TM2 machine, polynomial time in the input length n², maps the adjacency code of every G to the self-delimiting binary code of a ℤ-basis of Λ_G and of its Smith invariants; reason: polynomial bit complexity is model-robust; the input length n² is polynomial in n
--   - encoding: Smith invariants → positive s₁ ∣ ⋯ ∣ s_r with Λ_G = ⊕ ℤ s_i b_i for a basis b of ℤⁿ; reason: the standard characterization of the invariant factors of Λ_G ⊆ ℤⁿ
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.6 and (A.1), p.13 (PDF 14); proof §S8, pp.46–48 (PDF 47–49)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_Supplement_castVec
import Definitions.Def_IntADSat_Supplement_wordLatticeLE
import Definitions.Def_IntADSat_Supplement_degStar
import Definitions.Def_IntADSat_Supplement_graphCode
import Definitions.Def_IntADSat_Supplement_outputCode
import Definitions.Def_IntADSat_Supplement_IsSmithInvariants

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Theorem A.6 (Finite integral closure)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.13 (PDF 14); proof in §S8, pp.46–48 (PDF 47–49)).
Let `r = r_G` and `I_0 = [M_ℚ(G) ∩ ℤⁿ : Λ_{r−1}]`. Then `I_0` is finite and
`Λ_G = Λ_{r−1+⌊log₂ I_0⌋}`, `I_0 ≤ r^{r/2} Δ_*^{r(r−1)/2}`. In particular, all word vectors of length at most
`L = r − 1 + ⌈(r/2) log₂ r + (r(r−1)/2) log₂ Δ_*⌉` (A.1) generate `Λ_G`. A lattice basis and its Smith
invariants can be computed in deterministic polynomial time in the graph order.

**Formalization Note** `r_G = dim_ℚ M_ℚ(G)` (published `wordModule ℚ G`); `M_ℚ(G) ∩ ℤⁿ` is the pull-back of
`M_ℚ(G)` along `ℤⁿ ↪ ℚⁿ`; `I_0` is `AddSubgroup.relIndex` (which is `0` exactly when the index is infinite,
so "finite" is `0 < I_0`). `⌊log₂ I_0⌋ = Nat.log 2 I_0`; the powers in the bound are real powers. The
algorithm is a single Mathlib multi-stack Turing machine (`Turing.TM2ComputableInPolyTime`) on binary
strings, uniform in `n`, run on the `n²`-bit adjacency code `graphCode G`, whose output is the self-delimiting
binary code of a `ℤ`-basis `B` of `Λ_G` and of the Smith invariants `s` of `Λ_G ⊆ ℤⁿ`. Polynomial in the input
length `n²` is polynomial in `n`. Graphs have `n ≥ 1` vertices (standing assumption, p.11). -/
theorem theorem_A_6 :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)), 0 < n →
      let r := Module.finrank ℚ (IntADSat.wordModule ℚ G)
      let Sat : Submodule ℤ (Fin n → ℤ) :=
        ((IntADSat.wordModule ℚ G).restrictScalars ℤ).comap (castVec n)
      let I₀ := (wordLatticeLE G (r - 1)).toAddSubgroup.relIndex Sat.toAddSubgroup
      0 < I₀ ∧
      IntADSat.wordLattice G = wordLatticeLE G (r - 1 + Nat.log 2 I₀) ∧
      (I₀ : ℝ) ≤ (r : ℝ) ^ ((r : ℝ) / 2) * (degStar G : ℝ) ^ ((r : ℝ) * ((r : ℝ) - 1) / 2) ∧
      IntADSat.wordLattice G = wordLatticeLE G (r - 1 +
        ⌈(r : ℝ) / 2 * Real.logb 2 r + (r : ℝ) * ((r : ℝ) - 1) / 2 * Real.logb 2 (degStar G)⌉₊)) ∧
    ∃ f : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id f) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)), 0 < n →
        ∃ (B : List (Fin n → ℤ)) (s : List ℕ), f (graphCode G) = outputCode B s ∧
          LinearIndependent ℤ (fun i : Fin B.length => B.get i) ∧
          Submodule.span ℤ {x | x ∈ B} = IntADSat.wordLattice G ∧
          IsSmithInvariants (IntADSat.wordLattice G) s := by sorry

end IntADSat.Supplement
