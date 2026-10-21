-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_phi_strictAnti
-- name    : OpaqueQueue.Equilibrium.phi_strictAnti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:18.896535+00:00
-- url     : https://prove2.me/theorems/9aefedb2-a3bf-41bf-8eb9-c10a57b6f276
-- title:
--   Eq. (25) and footnote 2, p. 34 (PDF 35) — φn(π; θ) is decreasing in n
-- statement:
--   Under the standing assumptions, fix $x\in[0,1]$ and let
--   $$\varphi_n(x;\theta) = \frac{e^{v_n/\theta}-1}{x\,e^{v_n/\theta}+1-x},\qquad n\ge0, \tag{25}$$
--   so that $\partial f(x;q)/\partial x = \theta\sum_n g_n(q)\varphi_n(x;\theta)$. Then $n\mapsto\varphi_n(x;\theta)$ is strictly decreasing.
--
--   Together with Lemma 2, this is what makes the marginal value of joining smaller under a stochastically larger queue, hence the best response decreasing.
--
--   **Formalization Note** The paper says "decreasing"; the strict version is stated, which holds because $C>0$ makes $v_n$ strictly decreasing.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 34 (PDF 35), eq. (25), the sentence following it, and footnote 2

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem phi_strictAnti (P : Params) (hS : P.Standing) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : StrictAnti (phi P x) := by sorry
end OpaqueQueue.Equilibrium
