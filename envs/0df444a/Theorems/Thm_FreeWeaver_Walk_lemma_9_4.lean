-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_9_4
-- name    : FreeWeaver.Walk.lemma_9_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:37:47.797697+00:00
-- url     : https://prove2.me/theorems/f5f8bf61-712a-4808-94e3-d85aa258b38e
-- title:
--   Lemma 9.4 — the curvature step lowers the potential by κt_*²/5 and raises ‖x‖² by t_*²
-- statement:
--   In the setting of §9, let $(x,z)$ satisfy (9.2) with $z<60$, $|x_i|<1-\rho$ for every live $i$, (7.1) with $L=2/0.999^2$, and $\mathfrak m\ge1/16$. Then some unit $v$ supported on the live set has $x^Tv=0$ and $\mathcal F''[v,v]\le-3\kappa$. Moreover, for the direction $h$ and approximate potentials the walk obtains, the chosen point $x'\in\{x\pm t_*h\}$ satisfies: the segment from $x$ to $x'$ lies in the cube with $z>\lambda_+(\mathcal Y(y))$ at every point $y$ of it,
--   $$\mathcal F(x',z)\le\mathcal F(x,z)-\tfrac15\kappa t_*^2,\qquad\|x'\|_2^2=\|x\|_2^2+t_*^2 .$$
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the standing choices of §9: ε = max_i a_i, u = 128, the parameters (9.1), the smooth profile c_ζ with ζ = t_o/1000 → epsMax v, the literal 128, rho, tOut, zeta, eta, kappa, walkProfile n = smoothProfile 128 (zeta n); reason: the same quantities written out
--   - generalization: Algorithm 2 with the oracles of Appendix E.2 (Algorithm 3 and the procedure of Lemma E.8) → every oracle answer within the tolerances of Proposition E.4: q̂ with |q̂_i − q_i| ≤ η/(12u) and |𝔪̂ − 𝔪| ≤ 1/128, any unit h supported on the live set with xᵀh = 0 and ℱ''[h,h] < −κ/2, values of ℱ(x ± t_*h, z) to error κt_*²/96; reason: the paper says these tolerances are the only properties of the oracles used (p. 35); Algorithm 3's answers satisfy them (Proposition E.4), so the statement specializes to the paper's walk
--   - generalization: (x, z) satisfy (9.2) (z ≤ z₀ + the charges paid so far) → Inv92 … x z C for an arbitrary real C; reason: the charge history is not part of the lemma's data; with C the charges actually paid the hypothesis is the paper's, so the statement specializes to the paper's
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.4

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel
import Definitions.Def_FreeWeaver_Walk_Walk

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 36, Lemma 9.4 (Curvature step): "Let (x, z) satisfy (9.2) with z < 60, with
|xi| < 1 − ρ for every live i, and with (7.1) for L = 2/0.999^2 and semicircular mass 𝔪 ≥ 1/16.
Then there is a unit vector v, supported on the live coordinates, with x^T v = 0 and
ℱ''[v, v] ≤ −3κ. Moreover, Algorithm 2 computes a unit vector h, supported on the live coordinates,
with x^T h = 0, and the algorithm moves to the point x' ∈ {x + t∗h, x − t∗h} with the smaller
approximate value of the potential. The segment from x to x' lies in the cube, z > λ+(Y(y)) for
every point y of the segment, and ℱ(x', z) ≤ ℱ(x, z) − (1/5)κ t∗^2, ∥x'∥_2^2 = ∥x∥_2^2 + t∗^2."
Standing assumptions of §9 as in Lemma 9.1; `C` is the charge paid so far in (9.2). Algorithm 2's
direction and approximate potentials are every answer within the tolerances of Proposition E.4
(b)–(d): a unit `h` supported on the live set with `xᵀh = 0` and `ℱ''[h, h] < −κ/2`, and values
`F₊`, `F₋` of `ℱ(x ± t_* h, z)` to error `κt_*²/96`; `x'` is `x + t_* h` when `F₊ ≤ F₋`. -/
theorem lemma_9_4 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z C : ℝ)
    (hinv : Inv92 (walkProfile n) v s ω (epsMax v) x z C) (h60 : z < 60)
    (hlive : ∀ i, |x i| < 1 → |x i| < 1 - rho n)
    (h71 : Assumption71 (walkProfile n) v s ω x z 128 (2 / (0.999 : ℝ) ^ 2))
    (hms : 1 / 16 ≤ mass (walkProfile n) v s ω x z) :
    let ε := epsMax v
    let c := walkProfile n
    let ts := tStar n m ε
    (∃ w : Fin n → ℝ, ∑ i, w i ^ 2 = 1 ∧ (∀ i, ¬ |x i| < 1 → w i = 0) ∧
      ∑ i, x i * w i = 0 ∧ secondVar c v s ω x z w ≤ -3 * kappa n m) ∧
    ∀ (h : Fin n → ℝ) (Fp Fm : ℝ),
      ∑ i, h i ^ 2 = 1 → (∀ i, ¬ |x i| < 1 → h i = 0) → ∑ i, x i * h i = 0 →
      secondVar c v s ω x z h < -(kappa n m) / 2 →
      |Fp - potential c v s ω (x + ts • h) z| ≤ kappa n m * ts ^ 2 / 96 →
      |Fm - potential c v s ω (x - ts • h) z| ≤ kappa n m * ts ^ 2 / 96 →
      let x' := if Fp ≤ Fm then x + ts • h else x - ts • h
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
        (∀ i, |(x + τ • (x' - x)) i| ≤ 1) ∧ edge c v s (x + τ • (x' - x)) < z) ∧
      potential c v s ω x' z ≤ potential c v s ω x z - 1 / 5 * kappa n m * ts ^ 2 ∧
      ∑ i, x' i ^ 2 = ∑ i, x i ^ 2 + ts ^ 2 := by sorry

end FreeWeaver.Walk
