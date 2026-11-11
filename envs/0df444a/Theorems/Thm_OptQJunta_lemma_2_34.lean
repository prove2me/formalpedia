-- Prove2me | Theorems.Thm_OptQJunta_lemma_2_34
-- name    : OptQJunta.lemma_2_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:32.612934+00:00
-- url     : https://prove2.me/theorems/aba342f1-5040-45eb-9dad-40b604b3d6d3
-- title:
--   Lemma 2.34 — Fourier sampling: $H^{\otimes n}U_fH^{\otimes n}|0\rangle=\sum_S\widehat{(-1)^f}(S)|S\rangle$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ with $n\ge1$, let $H^{\otimes n}$ be the $n$-fold Hadamard transform and $U_f|x\rangle=(-1)^{f(x)}|x\rangle$. The unitary $A_f=H^{\otimes n}U_fH^{\otimes n}$ satisfies
--
--   $$
--   A_f|0\rangle=\sum_{S\subseteq[n]}\widehat{(-1)^f}(S)\,|S\rangle,
--   $$
--
--   where $|S\rangle$ is the incidence string of $S$. Both $A_f$ and $A_f^\dagger$ use one Boolean oracle query; formally, $A_f^\dagger=A_f$, and one standard query $O_f|x,b\rangle=|x,b\oplus f(x)\rangle$ maps $|x\rangle|-\rangle|\varphi\rangle$ to $(-1)^{f(x)}|x\rangle|-\rangle|\varphi\rangle$ for every workspace state $\varphi$ (phase kickback), so $U_f$ costs one query.
--
--   Measuring $A_f|0\rangle$ gives a Fourier sample; this is the reversible sampler to which Theorem 3.19 is applied.
--
--   Differences from the source:
--   - reading: "Both $A_f$ and $A_f^\dagger$ use one Boolean oracle query" → $A_f^\dagger=A_f$ and the phase-kickback identity $O_f(|x\rangle|-\rangle|\varphi\rangle)=(-1)^{f(x)}|x\rangle|-\rangle|\varphi\rangle$; reason: these are the two facts that make the query cost one (the proof on p.25: "Phase kickback implements $U_f$ with one Boolean query, and $U_f$ is self-inverse"); a query count needs a circuit model, which these identities give
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 2.34, p.25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_infl
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Lemma 2.34** (Fourier sampling [AS07]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.25). Let `f : {0,1}^n → {0,1}`, where `n ≥ 1`.
The unitary `A_f = H^{⊗n} U_f H^{⊗n}` satisfies `A_f|0⟩ = Σ_{S ⊆ [n]} \widehat{(−1)^f}(S) |S⟩`. Both `A_f`
and `A_f†` use one Boolean oracle query.

**Formalization Note** `H^{⊗n}` is `QAlgorithms.hadamardN n`, `U_f |x⟩ = (−1)^{f(x)} |x⟩` is
`QAlgorithms.phaseOracle f`, `|0⟩` is `zeroKet n`, and `|S⟩` is the basis state of the incidence
string of `S`. "Both `A_f` and `A_f†` use one Boolean oracle query" is stated by its two facts:
(2) `A_f† = A_f`, and (3) phase kickback: one standard query `O_f |x, b⟩ = |x, b ⊕ f(x)⟩` (with
any workspace) maps `|x⟩|−⟩|φ⟩` to `(−1)^{f(x)} |x⟩|−⟩|φ⟩`, so `U_f` costs one query. -/
theorem lemma_2_34 {n : ℕ} (hn : 1 ≤ n) (f : Qubits n → Bool) :
    act (hadamardN n * phaseOracle f * hadamardN n) (zeroKet n) =
        ∑ S : Finset (Fin n), ((fourierSign f S : ℝ) : ℂ) • ket (fun i => decide (i ∈ S)) ∧
      (hadamardN n * phaseOracle f * hadamardN n).conjTranspose =
        hadamardN n * phaseOracle f * hadamardN n ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (x : Qubits n) (φ : EuclideanSpace ℂ W),
        act (Matrix.kronecker (xorOracle f) (1 : Matrix W W ℂ))
            (tensorVec (tensorVec (ket x) minusKet) φ) =
          ((signFn f x : ℝ) : ℂ) • tensorVec (tensorVec (ket x) minusKet) φ := by sorry

end OptQJunta
