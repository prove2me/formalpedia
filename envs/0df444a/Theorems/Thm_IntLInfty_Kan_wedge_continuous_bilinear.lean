-- Prove2me | Theorems.Thm_IntLInfty_Kan_wedge_continuous_bilinear
-- name    : IntLInfty.Kan.wedge_continuous_bilinear
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:42.141235+00:00
-- url     : https://prove2.me/theorems/d2ebe931-a930-48f2-b5a5-4d16e8ae7a23
-- title:
--   The wedge product of $C^r$ jets is a continuous bilinear map; cone Gronwall
-- statement:
--   (i) For $r\ge1$ there are continuous bilinear maps $W_{p,q}:\Omega^p_{C^r}(\Delta^m)\times\Omega^q_{C^r}(\Delta^m)\to\Omega^{p+q}_{C^r}(\Delta^m)$ on jets with $$W(j^r\alpha,j^r\beta)=j^r(\alpha\wedge\beta),$$ and $(w_1,w_2)\mapsto W(w_1,w_2)$ is $C^\infty$. (ii) (Gronwall along rays) If $S$ is star-shaped about $0$, $B$ is continuous and bounded on $S$ and $\|B(x)\|\le C\|x\|\int_0^1\|B(tx)\|dt$ on $S$, then $B=0$ on $S$.
--
--   Role: the smooth wedge product and the vanishing lemma used for smooth families of forms and for integrality (K0b).
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem wedge_continuous_bilinear :
    (∀ {m r : ℕ}, 1 ≤ r → ∃ W : ∀ p q : ℕ, CrForms r m p →L[ℝ] CrForms r m q →L[ℝ] CrForms r m (p + q), (∀ (p q : ℕ) (w1 : CrForms r m p) (w2 : CrForms r m q) (α β : Ω m), IsDeg p α ∧ IsCr r α → IsDeg q β ∧ IsCr r β → jet r α = w1 → jet r β = w2 → (W p q w1 w2 : Jet r m × Jet r m) = jet r (α * β)) ∧ ∀ p q : ℕ, ContDiff ℝ ∞ (fun x : CrForms r m p × CrForms r m q => W p q x.1 x.2)) ∧
    (∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] {S : Set E}, (∀ x ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ S) → ∀ B : E → F, ContinuousOn B S → ∀ {M : ℝ}, (∀ x ∈ S, ‖B x‖ ≤ M) → ∀ {C : ℝ}, 0 ≤ C → (∀ x ∈ S, ‖B x‖ ≤ C * ‖x‖ * ∫ t in (0 : ℝ)..1, ‖B (t • x)‖) → ∀ x ∈ S, B x = 0) := by sorry

end IntLInfty.Kan
