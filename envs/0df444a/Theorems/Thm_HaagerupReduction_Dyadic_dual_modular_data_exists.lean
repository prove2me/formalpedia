-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_dual_modular_data_exists
-- name    : HaagerupReduction.Dyadic.dual_modular_data_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:04.060991+00:00
-- url     : https://prove2.me/theorems/6bc21fe2-409d-4ef7-b8bf-5ba59fb4246f
-- title:
--   (1.7) and §2, pp. 4–6 — the dual state φ̂ on R = M ⋊_{σ^ϕ} G has modular data: ξ̂ = δ_0 ⊗ ξ is cyclic and separating for R
-- statement:
--   Let $(M,\varphi)$ be a von Neumann algebra on $H$ in standard form with normal faithful state $\varphi(x) = \langle x\xi,\xi\rangle$, let $G = \bigcup_{n\ge1}2^{-n}\mathbb Z$, and let $\mathcal R = M\rtimes_{\sigma^\varphi} G$ act on $\ell^2(G,H)$, with $\hat\xi = \delta_0\otimes\xi$ and dual state $\hat\varphi(y) = \langle y\hat\xi,\hat\xi\rangle$.
--
--   Then $(\mathcal R, \hat\varphi)$ is again in standard form: there exist modular data $\hat S$ on $\ell^2(G,H)$, that is, a unit vector cyclic and separating for $\mathcal R$, a modular operator $\hat\Delta$ and a modular conjugation $\hat J$ satisfying the closed Tomita relation $\overline{\{(y\hat\xi, y^*\hat\xi) : y\in\mathcal R\}} = \operatorname{graph}(\hat J\hat\Delta^{1/2})$, with
--   $$\hat S.M = \mathcal R, \qquad \hat S.\xi = \hat\xi .$$
--
--   This is the statement that $\hat\varphi$ is a normal faithful state on $\mathcal R$ (p. 6) together with the existence of its modular automorphism group $\sigma^{\hat\varphi}$, used throughout §2. It also shows that the hypotheses on $\hat S$ in the other statements of this mission can be met.
--
--   **Formalization Note.** Modular data are the published `OAI.BoundedRecovery.StandardModularData`. The paper takes Tomita–Takesaki theory for granted; since the platform has no existence theorem, the existence for the dual state is a separate statement here.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 4, display (1.7) and (1.9); p. 6, 'Recall that φ̂ is a normal faithful state on R'

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Existence of the modular data of the dual state `φ̂` on `R = M ⋊_{σ^ϕ} G`. -/
theorem dual_modular_data_exists {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) :
    ∃ Sh : StandardModularData (L2G H), Sh.M = crossedProduct S ∧ Sh.xi = xiHat S := by sorry

end HaagerupReduction.Dyadic
