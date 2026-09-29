-- Prove2me | Theorems.Thm_GelfondSchneider_deriv_identity
-- name    : GelfondSchneider.deriv_identity
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:53.036741+00:00
-- url     : https://prove2.me/theorems/c21422a2-1acb-478f-8fd1-ae8ea5b082f4
-- title:
--   Derivatives of Gelfond's auxiliary function at the integers
-- statement:
--   Let $\sigma : K \to \mathbb C$ with $\sigma(\beta') = \beta$, $\sigma(\alpha') = e^{l}$ and $\sigma(\gamma') = e^{\beta l}$. For coefficients $\eta_{ab} \in K$ put $E(z) = \sum_{a,b} \sigma(\eta_{ab})\, e^{(a + b\beta) l z}$. Then for every $k$ and every natural number $j$,
--
--   $$E^{(k)}(j) = l^{k}\, \sigma\!\left(\sum_{a,b} \eta_{ab}\,(a + b\beta')^{k}\,\alpha'^{\,aj}\,\gamma'^{\,bj}\right).$$
--
--   So the derivatives of the auxiliary function at the integers are, up to the factor $l^k$, images of elements of $K$.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem deriv_identity (K : Type*) [Field K] (σ : K →+* ℂ) (α' β' γ' : K) (l β : ℂ)
    (hβ : σ β' = β) (hα : σ α' = Complex.exp l) (hγ : σ γ' = Complex.exp (β * l))
    (q : ℕ) (η : Fin q → Fin q → K) (k j : ℕ) :
    iteratedDeriv k (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
        σ (η a b) * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (j : ℂ) =
      l ^ k * σ (∑ a : Fin q, ∑ b : Fin q, η a b *
        (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
        α' ^ (((a : ℕ) + 1) * j) * γ' ^ (((b : ℕ) + 1) * j)) := by
  sorry

end GelfondSchneider
