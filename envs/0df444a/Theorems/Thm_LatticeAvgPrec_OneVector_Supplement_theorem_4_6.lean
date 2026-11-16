-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_theorem_4_6
-- name    : LatticeAvgPrec.OneVector.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:43:06.25045+00:00
-- url     : https://prove2.me/theorems/3b537933-5fb5-4f2c-9b63-1d991906b934
-- title:
--   Theorem 4.6 — Prefix extraction from a Smith massager
-- statement:
--   Fix $2<\omega\le3$ available and a constant $c_1\ge1$ (the constant of the hypothesis "$O(p)$ bits"). There are a deterministic program $\mathcal P$, a constant $c>0$ and a subpolynomial factor $g$ such that the following holds.
--
--   Let $H\in\mathbb Z^{r\times r}$, $r\ge1$, be nonsingular, $\Gamma=\Lambda(H)$, and let $(S,F)$, $S=\mathrm{diag}(s_1,\dots,s_m)$, be a reduced Smith massager for $H$; put $D=\log_2\det\Gamma=\sum_j\log_2 s_j$. Let $V_0\in\mathbb Z^{r\times r}$ be nonsingular, $d\ge1$ an integer, $V=V_0/d$, $p\ge1$, with every entry of $V_0$ and $d$ of at most $c_1p$ bits and $\|V\|_2,\|V^{-1}\|_2\le2^p$. Let $B\ge1$ be an integer. On input $(S,F,V_0,d,p,B)$, $\mathcal P$ outputs $X\in\mathbb Z^{r\times s}$ (possibly $s=0$) with:
--
--   1. the columns of $X$ are linearly independent;
--   2. $\{z\in\Gamma:\|Vz\|_2\le B\}\subseteq X\mathbb Z^s=\Gamma\cap\mathrm{span}_{\mathbb R}X$;
--   3. $VX$ meets Definition 4.5 for $V\Gamma$ at radius $B$: $\{y\in V\Gamma:\|y\|_2\le B\}\subseteq VX\mathbb Z^s\subseteq V\Gamma$ and $\|VX_i\|_2\le2^{cr\log_2(2r)}B$;
--   4. for every $i$,
--   $$\|VX_i\|_2\le 2^{cr}B,\qquad \|VX_i\|_2\le2^{cr}\lambda_i(V\Gamma);$$
--   5. every entry of $X$ has at most $c\,(p+\log_2B+r)$ bits, independently of $D$;
--
--   within
--
--   $$
--   g\bigl(r,\lceil D\rceil+p+\lceil\log_2B\rceil\bigr)\,\bigl(r^{\omega-1}D+r^{\omega}(p+\log_2B+r)\bigr)
--   $$
--
--   bit operations, input and output included (11).
--
--   The theorem isolates the step that retains every short lattice direction at a cost driven by the average precision $D/r$; it is the prefix step of the complete-basis algorithm and yields a bounded short-span extraction algorithm in expected $\widetilde O(r^{\omega}\beta)$ for $\beta$-bit inputs (p.17).
--
--   **Formalization Note** The program sees only the massager, $V_0$, $d$, $p$ and $B$, never $H$. The hypothesis constant $c_1$ is quantified before the program; the conclusion's constants are chosen after it and before every input. Columns of $X$ are indexed from $0$, so column $i$ is compared with $\lambda_{i+1}(V\Gamma)$. $\widetilde O$ follows the conventions of §1.1.1 (p.4), as in the published goal: $\widetilde O$ suppresses a subpolynomial factor in the dimension and precision parameters, chosen with the program after $\omega$ and before every input.
--
--   Differences from the source:
--   - reading: entries of V_0 and d have O(p) bits → ∀ c₁ ≥ 1, quantified before the program: bits ≤ c₁ p; reason: a constant inside a hypothesis is universal; c₁ < 1 is covered by c₁ = 1
--   - reading: "the prefix operation in Steps 2–3 returns …", cost (11) without "expected" → ∃ coin-free program (DeterministicWithin) reading (S, F, V_0, d, p, B); reason: Steps 2–3 consist of Lemma 3.1 and Lemma 4.4, both deterministic; the theorem states a cost, not an expected cost
--   - encoding: (S, F) a reduced Smith massager for a basis of Γ ⊆ ℤ^r, D = log det Γ → Γ = lat H for nonsingular H with IsReducedSmithMassager H s F; D = Σ_j log₂ s_j; reason: ∏ s_j = det Γ by Definition 2.3; m = 0 (Γ = ℤ^r) included
--   - reading: 2^{O(r log(2r))}, 2^{O(r)}, O(p + log B + r) and Õ(·) → one constant c for all three, and g(r, ⌈D⌉ + p + ⌈log₂ B⌉) subpolynomial; reason: one constant can be taken as the maximum; the Õ convention of §1.1.1
--   - encoding: λ_i(VΓ), X_i for 1 ≤ i ≤ s → column i ∈ Fin s against lamV V (lat H) (i+1); reason: Lean indexes columns from 0
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 4.6 and Definition 4.5, p.16 (proof p.16)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Theorem 4.6** (Prefix extraction from a Smith massager; STOC 2027 submission #1574, p.16).
Let `(S, F)` be a reduced Smith massager for a basis of `Γ ⊆ ℤ^r`, with `m` moduli and
`D = log det Γ`. Let `V = V_0/d ∈ ℚ^{r×r}` be nonsingular, where the entries of `V_0 ∈ ℤ^{r×r}` and
the positive integer `d` have `O(p)` bits, with `‖V‖₂, ‖V⁻¹‖₂ ≤ 2^p` and `p ≥ 1`. For any integer
radius `B ≥ 1`, the prefix operation returns an integer `X ∈ ℤ^{r×s}` such that `VX` meets
Definition 4.5 for `VΓ` at radius `B`, `{z ∈ Γ : ‖Vz‖₂ ≤ B} ⊆ Xℤ^s = Γ ∩ span_ℝ X`,
`‖VX_i‖₂ ≤ 2^{O(r)} B`, `‖VX_i‖₂ ≤ 2^{O(r)} λ_i(VΓ)`; the entries of `X` have `O(p + log B + r)`
bits, independently of `D`; the cost is `Õ(r^{ω−1}D + r^ω(p + log B + r))` (11).

**Formalization Note** `Γ = Λ(H)` for a nonsingular `H`; the program sees only `s, F, V_0, d, p, B`.
The constant `c₁` of the hypothesis "`O(p)` bits" is universally quantified first; the program, the
constant `c` of every `O(·)` in the conclusion and the subpolynomial factor `g` of `Õ` come after it
and before every input. The operation is deterministic. `D = Σ_j log₂ s_j`. Columns of `X` are
indexed from `0`, so column `i` is compared with `λ_{i+1}`. -/
theorem theorem_4_6 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω)
    (c₁ : ℝ) (hc₁ : 1 ≤ c₁) :
    ∃ (P : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
      ∀ (r m : ℕ) (H : Matrix (Fin r) (Fin r) ℤ) (s : Fin m → ℕ) (F : Matrix (Fin r) (Fin m) ℤ)
        (V₀ : Matrix (Fin r) (Fin r) ℤ) (d p B : ℕ),
        1 ≤ r → H.det ≠ 0 → IsReducedSmithMassager H s F →
        1 ≤ d → 1 ≤ p → 1 ≤ B → V₀.det ≠ 0 →
        (∀ i j, (bits (V₀ i j) : ℝ) ≤ c₁ * p) → (bits (d : ℤ) : ℝ) ≤ c₁ * p →
        specNorm ((d : ℝ)⁻¹ • rmat V₀) ≤ (2 : ℝ) ^ p →
        specNorm ((d : ℝ)⁻¹ • rmat V₀)⁻¹ ≤ (2 : ℝ) ^ p →
        SoftmaxAttnFD.DeterministicWithin P
          (TimeSpaceMA.memOf (vecCode (fun j => (s j : ℤ)) ++ matCode F ++ matCode V₀ ++
            natCode d ++ natCode p ++ natCode B))
          (fun mem => ∃ (k : ℕ) (X : Matrix (Fin r) (Fin k) ℤ), memHolds mem (matCode X) ∧
            LinearIndependent ℝ (fun i => fun t => ((X t i : ℤ) : ℝ)) ∧
            {z | z ∈ lat H ∧
                l2 (((d : ℝ)⁻¹ • rmat V₀) *ᵥ fun t => ((z t : ℤ) : ℝ)) ≤ B} ⊆ lat X ∧
            lat X = {z | z ∈ lat H ∧ (fun t => ((z t : ℤ) : ℝ)) ∈
                Submodule.span ℝ (Set.range fun i => fun t => ((X t i : ℤ) : ℝ))} ∧
            IsShortSpanExt c r
              ((fun z : Fin r → ℤ => ((d : ℝ)⁻¹ • rmat V₀) *ᵥ fun t => ((z t : ℤ) : ℝ)) '' lat H)
              B (fun i => ((d : ℝ)⁻¹ • rmat V₀) *ᵥ fun t => ((X t i : ℤ) : ℝ)) ∧
            (∀ i : Fin k,
              l2 (((d : ℝ)⁻¹ • rmat V₀) *ᵥ fun t => ((X t i : ℤ) : ℝ)) ≤ (2 : ℝ) ^ (c * r) * B ∧
              l2 (((d : ℝ)⁻¹ • rmat V₀) *ᵥ fun t => ((X t i : ℤ) : ℝ)) ≤
                (2 : ℝ) ^ (c * r) * lamV ((d : ℝ)⁻¹ • rmat V₀) (lat H) ((i : ℕ) + 1)) ∧
            ∀ i j, (bits (X i j) : ℝ) ≤ c * ((p : ℝ) + Real.logb 2 B + r))
          (g r (⌈∑ j, Real.logb 2 (s j)⌉₊ + p + Nat.clog 2 B) *
            ((r : ℝ) ^ (ω - 1) * (∑ j, Real.logb 2 (s j)) +
              (r : ℝ) ^ ω * ((p : ℝ) + Real.logb 2 B + r))) := by sorry

end LatticeAvgPrec.OneVector.Supplement
