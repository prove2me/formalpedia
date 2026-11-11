-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_9_1
-- name    : FreeWeaver.Walk.lemma_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:38:05.407667+00:00
-- url     : https://prove2.me/theorems/a04db740-02c9-4bd5-a078-1921f2e180a0
-- title:
--   Lemma 9.1 — boundary rounding of a coordinate within ρ of ±1 at charge ε(1 − |x_i|) ≤ ερ
-- statement:
--   In the setting of §9, let $x\in[-1,1]^n$, $z>\lambda_+(\mathcal Y(x))$, $\mathcal F(x,z)\le B$, and $i$ live with $|x_i|\ge1-\rho$. With $x'$ equal to $x$ except $x'_i=\operatorname{sgn}(x_i)$ and $z'=z+\varepsilon(1-|x_i|)$: $z'>\lambda_+(\mathcal Y(x'))$, $\mathcal F(x',z')\le\mathcal F(x,z)\le B$, $\|x'\|_2^2>\|x\|_2^2$, and the charge satisfies
--   $$\varepsilon(1-|x_i|)\le\varepsilon\rho .$$
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the standing choices of §9: ε = max_i a_i, u = 128, the parameters (9.1), the smooth profile c_ζ with ζ = t_o/1000 → epsMax v, the literal 128, rho, tOut, zeta, eta, kappa, walkProfile n = smoothProfile 128 (zeta n); reason: the same quantities written out
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.1

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel
import Definitions.Def_FreeWeaver_Walk_Walk

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.1 (Boundary rounding): "Let z > λ+(Y(x)), let ℱ(x, z) ≤ B, and let i be
live with |xi| ≥ 1 − ρ. Let x' be x with xi replaced by sgn(xi), and let z' = z + ε(1 − |xi|). Then
z' > λ+(Y(x')) and ℱ(x', z') ≤ ℱ(x, z), so ℱ(x', z') ≤ B. Also ∥x'∥_2^2 > ∥x∥_2^2. The charge is at
most ερ."
Standing assumptions of §9: `ε = max_i ‖v_i‖²`, `u = 128`, the parameters (9.1), the smooth profile
`c_ζ` with `ζ = t_o/1000`; `x ∈ [−1, 1]^n` is a state. -/
theorem lemma_9_1 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z : ℝ)
    (hz : edge (walkProfile n) v s x < z)
    (hF : potential (walkProfile n) v s ω x z ≤ budget 128 (epsMax v))
    (i : Fin n) (hi : |x i| < 1) (hi' : 1 - rho n ≤ |x i|) :
    let ε := epsMax v
    let c := walkProfile n
    let x' := Function.update x i (sgn (x i))
    let z' := z + ε * (1 - |x i|)
    edge c v s x' < z' ∧ potential c v s ω x' z' ≤ potential c v s ω x z ∧
      potential c v s ω x' z' ≤ budget 128 ε ∧
      ∑ j, x j ^ 2 < ∑ j, x' j ^ 2 ∧ ε * (1 - |x i|) ≤ ε * rho n := by sorry

end FreeWeaver.Walk
