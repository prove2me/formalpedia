-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_dual_modular_group
-- name    : HaagerupReduction.Dyadic.dual_modular_group
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:03.523545+00:00
-- url     : https://prove2.me/theorems/3fb7befd-7967-4591-9d5d-5499a21481fd
-- title:
--   (1.7), p. 4 — σ^φ̂_t(π(x)) = π(σ^ϕ_t(x)) and σ^φ̂_t(λ(g)) = λ(g)
-- statement:
--   Let $(M,\varphi)$, $G$, $\mathcal R = M\rtimes_{\sigma^\varphi}G$ on $\ell^2(G,H)$, $\pi$, $\lambda$, $\hat\xi = \delta_0\otimes\xi$ and $\hat\varphi$ be as in the model, and let $\hat S$ be modular data of $(\mathcal R,\hat\varphi)$, i.e. with $\hat S.M = \mathcal R$ and $\hat S.\xi = \hat\xi$; write $\sigma^{\hat\varphi}_t(y) = \hat\Delta^{it}y\hat\Delta^{-it}$. Then for all $t \in\mathbb R$, $x\in M$, $g\in G$,
--   $$\sigma^{\hat\varphi}_t(\pi(x)) = \pi(\sigma^\varphi_t(x)), \qquad \sigma^{\hat\varphi}_t(\lambda(g)) = \lambda(g).$$
--
--   Thus $\sigma^{\hat\varphi}$ fixes the translations and restricts to $\sigma^\varphi$ on $\pi(M)\cong M$. Together with (1.1) it gives $\sigma^{\hat\varphi}_s = \operatorname{Ad}\lambda(s)$ for $s\in G$ (display (2.2)), on which Lemma 2.3 rests.
--
--   **Formalization Note.** The modular data of $\hat\varphi$ are a hypothesis $\hat S$ (their existence is `dual_modular_data_exists`), not a formula: the identity above is what the statement asserts.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 4, display (1.7)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- (1.7): `σ^φ̂_t(π(x)) = π(σ^ϕ_t(x))` and `σ^φ̂_t(λ(g)) = λ(g)`. -/
theorem dual_modular_group {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H)
    (Sh : StandardModularData (L2G H)) (hM : Sh.M = crossedProduct S) (hxi : Sh.xi = xiHat S) :
    (∀ t : ℝ, ∀ x ∈ S.M, Sh.sigma t (piOp S x) = piOp S (S.sigma t x)) ∧
    (∀ t : ℝ, ∀ g : dyadic, Sh.sigma t (lam H g) = lam H g) := by sorry

end HaagerupReduction.Dyadic
