-- Prove2me | Theorems.Thm_KTCenter_lemma_5_8
-- name    : KTCenter.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:56.67225+00:00
-- url     : https://prove2.me/theorems/038fa466-b413-439d-aa78-9bd2e0e96da9
-- title:
--   Lemma 5.8 — $|F|,|\mathcal B_\ell|\le4C_1^2\ell/\gamma^2$, $\mathcal B^\prime$ partitions $U^\prime$, and (32) (corrected: $|\mathcal P(F)|$ bound for $K\ge1$)
-- statement:
--   Let $I$ be a cost instance with key bound $K$ and positive constants $C_0,C_1$, and $0<\xi<1$, with $\gamma,\ell,\theta,F,U',\mathcal B',\mathcal B_\ell$ as in (28). Then:
--
--   1. $|F|\le4C_1^2\ell/\gamma^2$, $|\mathcal B_\ell|\le4C_1^2\ell/\gamma^2$, and, when $K\ge1$, $|\mathcal P(F)|\le K^{4C_1^2\ell/\gamma^2}$;
--   2. $\mathcal B'$ partitions $U'$ into nonempty subsets, $\sum_{B\in\mathcal B'}|B|^2\le Q_0$ and $\sum_{v\in U'}\lambda_v\le\Lambda$;
--   3. for every $\varphi\in\mathcal P(F)$, $p'\in\mathcal P(U')$ and $i$: $\tilde C^\varphi_i(p')=\tilde C_i(\varphi\cup p')$ (32);
--   4. for every $\varphi$, $i$, $v\in U'$ and $p',r'\in\mathcal P(U')$ agreeing outside $v$: $|\tilde C^\varphi_i(p')-\tilde C^\varphi_i(r')|\le\lambda_v\le\theta$.
--
--   Differences from the source:
--
--   - correction: |𝒫(F)| ≤ K^{4C₁²ℓ/γ²} → the same bound under the premise 1 ≤ K, on that clause only; reason: the printed bound is false for a cost instance with U = ∅ and K = 0, which satisfies every assumption of p.15 (each |P_v|, v ∈ U, is at most K vacuously): there 𝒫(F) = 𝒫(∅) has one element and 0^{4C₁²ℓ/γ²} = 0; every instance with a variable has K ≥ 1, so nothing else changes
--   - encoding: K^{4C₁²ℓ/γ²} with a possibly non-integer exponent → real power Real.rpow; reason: Lean convention; same value
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.8, eq. (32), p.38 (PDF p.40)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_FixKeys

namespace KTCenter

/-- **Lemma 5.8** (Bounds and exact costs after fixing keys), eq. (32), p.38 (PDF p.40).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** For any cost instance satisfying (7). `4C₁²ℓ/γ²` need not be an integer, so
the bound on `|𝒫(F)|` is a real power. That clause carries the premise `1 ≤ K`: with no variables
the source's assumptions admit `K = 0`, where `|𝒫(F)| = |𝒫(∅)| = 1 > 0 = K^{4C₁²ℓ/γ²}`; every
instance with a variable has `K ≥ 1`. -/
theorem lemma_5_8 {K : ℕ} {C₀ C₁ : ℚ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (I : CostInstance K C₀ C₁) (ξ : ℚ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((I.F ξ).card : ℚ) ≤ 4 * C₁ ^ 2 * (I.ell : ℚ) / CostInstance.gamma ξ ^ 2 ∧
    ((I.bLarge ξ).card : ℚ) ≤ 4 * C₁ ^ 2 * (I.ell : ℚ) / CostInstance.gamma ξ ^ 2 ∧
    (1 ≤ K → (Fintype.card (I.AssignOn (I.F ξ)) : ℝ) ≤
      (K : ℝ) ^ (((4 * C₁ ^ 2 * (I.ell : ℚ) / CostInstance.gamma ξ ^ 2 : ℚ)) : ℝ)) ∧
    (∀ B ∈ I.blocksRes ξ, B.Nonempty ∧ B ⊆ I.Ures ξ) ∧
    (↑(I.blocksRes ξ) : Set (Finset (Fin I.N))).PairwiseDisjoint id ∧
    (I.blocksRes ξ).biUnion id = I.Ures ξ ∧
    (∑ B ∈ I.blocksRes ξ, B.card ^ 2) ≤ I.Q0 ∧
    ∑ v ∈ I.Ures ξ, I.lam v ≤ I.Lam ∧
    (∀ (φ : I.AssignOn (I.F ξ)) (p' : I.AssignOn (I.Ures ξ)) (i : Fin I.n),
      I.costPhi ξ φ i p' = I.cost i (I.union ξ φ p')) ∧
    (∀ (φ : I.AssignOn (I.F ξ)) (i : Fin I.n) (v : {v // v ∈ I.Ures ξ})
        (p' r' : I.AssignOn (I.Ures ξ)), (∀ u, u ≠ v → p' u = r' u) →
      |I.costPhi ξ φ i p' - I.costPhi ξ φ i r'| ≤ I.lam v ∧ I.lam v ≤ I.theta ξ) := by sorry

end KTCenter
