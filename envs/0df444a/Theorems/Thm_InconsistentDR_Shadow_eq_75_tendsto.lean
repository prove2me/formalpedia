-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_eq_75_tendsto
-- name    : InconsistentDR.Shadow.eq_75_tendsto
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T22:54:23.877219+00:00
-- url     : https://prove2.me/theorems/e5719cb5-63a7-44de-b88e-eeeb6de7406a
-- title:
--   (75), p. 24 — the Douglas–Rachford shadow differences $P_fT^nx-P_gR_fT^nx=T^nx-T^{n+1}x$ converge to the minimal displacement vector $v$
-- statement:
--   Let $X$ be a real Hilbert space, let $f, g \in \Gamma_0(X)$, and let $P_f = (\mathrm{Id}+\partial f)^{-1}$, $P_g = (\mathrm{Id}+\partial g)^{-1}$ be their proximal mappings, $R_f = 2P_f - \mathrm{Id}$. Let
--   $$T = \mathrm{Id} - P_f + P_g R_f$$
--   be the Douglas–Rachford operator and let $v = P_{\overline{\operatorname{ran}}(\mathrm{Id}-T)}(0)$ be its minimal displacement vector (the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$). Then for every $x \in X$ and every $n \in \mathbb{N}$,
--   $$P_f T^n x - P_g R_f T^n x = T^n x - T^{n+1} x,$$
--   and
--   $$T^n x - T^{n+1} x \to v \quad (n \to \infty)$$
--   in norm.
--
--   The identity is immediate from the definition of $T$. The limit is the Baillon–Bruck–Reich / Pazy asymptotic-regularity theorem for the firmly nonexpansive operator $T$ (the paper cites (58), p. 17, which refers to Bruck–Reich, *Nonexpansive projections and resolvents of accretive operators in Banach spaces*, Houston J. Math. 3 (1977), Corollary 1.5, together with [6, Example 23.3] identifying $P_f, P_g$ as the resolvents of $\partial f, \partial g$).
--
--   **Formalization note.** $f,g$ are `X → EReal` functions satisfying `GammaZero`; the proximal maps are given as maps `Pf Pg : X → X` with `IsResolvent 1 (subgrad f) Pf`; $T$ is `drT Pf Pg`, $R_f$ is `refl Pf`; $v$ is given by `IsMinNormPt` on the closure of the range of $\mathrm{Id}-T$. The standing assumption (12) and (74) of §6 are not needed for (75) and are omitted.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 24, display (75) (from (58), p. 17, and [6, Example 23.3]; limit by Bruck–Reich 1977, Corollary 1.5)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization

/-- (75), p. 24 (from (58), p. 17, and [6, Example 23.3]): for `f, g ∈ Γ₀(X)` with proximal maps
`P_f, P_g`, `T = drT P_f P_g` and `v` the least-norm point of `cl ran(Id − T)`, for every `x`,
`P_f Tⁿx − P_g R_f Tⁿx = Tⁿx − Tⁿ⁺¹x → v`. -/
theorem eq_75_tendsto {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v) (x : X) :
    (∀ n : ℕ, Pf ((drT Pf Pg)^[n] x) - Pg (refl Pf ((drT Pf Pg)^[n] x)) =
      (drT Pf Pg)^[n] x - (drT Pf Pg)^[n + 1] x) ∧
    Tendsto (fun n : ℕ => (drT Pf Pg)^[n] x - (drT Pf Pg)^[n + 1] x) atTop (𝓝 v) := by sorry

end InconsistentDR.Shadow
