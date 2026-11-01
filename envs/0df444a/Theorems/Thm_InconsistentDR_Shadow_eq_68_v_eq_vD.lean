-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_eq_68_v_eq_vD
-- name    : InconsistentDR.Shadow.eq_68_v_eq_vD
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T23:32:05.044513+00:00
-- url     : https://prove2.me/theorems/893917b7-0171-4d4e-984e-12e394ecc9ec
-- title:
--   (68), p. 22 — if $v_R=0$ then the minimal displacement vector $v$ equals $v_D=P_{\overline D}(0)$
-- statement:
--   Let $X$ be a real Hilbert space and $f,g\in\Gamma_0(X)$, with proximal mappings $P_f=(\mathrm{Id}+\partial f)^{-1}$, $P_g=(\mathrm{Id}+\partial g)^{-1}$, $R_f=2P_f-\mathrm{Id}$, and Douglas–Rachford operator
--   $$T=\mathrm{Id}-P_f+P_gR_f .$$
--   Let $v$ be the minimal displacement vector, i.e. the least-norm point of $\overline{\operatorname{ran}}(\mathrm{Id}-T)$, and set
--   $$D=\operatorname{dom}\partial f-\operatorname{dom}\partial g,\qquad R=\operatorname{ran}\partial f+\operatorname{ran}\partial g .$$
--   Assume the standing assumption (12), $\overline{\operatorname{ran}}(\mathrm{Id}-T)=\overline{D\cap R}=\overline D\cap\overline R$, and that $v_R:=P_{\overline R}(0)=0$, i.e. $0\in\overline R$. Then $v$ is also the least-norm point of $\overline D$:
--   $$v=v_D=P_{\overline D}(0).$$
--
--   This is display (68) of §6 (p. 22), which follows from Proposition 3.3(vii), $v=v_D+v_R$. It is used throughout §6, in particular for (70), Lemma 6.3 and Proposition 6.6.
--
--   **Formalization Note** $f,g$ are `X → EReal` functions satisfying `GammaZero`; $P_f,P_g$ are maps with `IsResolvent 1 (subgrad f) Pf`; $T$ is `drT Pf Pg`. Least-norm points are encoded by the published `IsMinNormPt`; $D$ and $R$ are `setD` and `setR` of the subdifferentials. The hypothesis $v_R=0$ is written $0\in\overline R$, which is equivalent.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 22, display (68) (consequence of Proposition 3.3(vii), p. 10)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence MoreauProx.Characterization

/-- (68), p. 22: for `f, g ∈ Γ₀(X)`, under (12), if `v_R = P_{cl R}(0) = 0` (i.e. `0 ∈ cl R`),
then `v = P_{cl ran(Id − T)}(0)` is also the least-norm point `v_D` of `cl D = cl(dom ∂f − dom ∂g)`. -/
theorem eq_68_v_eq_vD {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (Pf Pg : X → X) (hPf : IsResolvent 1 (subgrad f) Pf) (hPg : IsResolvent 1 (subgrad g) Pg)
    (v : X) (hv : IsMinNormPt (closure (Set.range fun x => x - drT Pf Pg x)) v)
    (h12 : Standing12 (subgrad f) (subgrad g) Pf Pg)
    (hvR : (0 : X) ∈ closure (setR (subgrad f) (subgrad g))) :
    IsMinNormPt (closure (setD (subgrad f) (subgrad g))) v := by sorry

end InconsistentDR.Shadow
