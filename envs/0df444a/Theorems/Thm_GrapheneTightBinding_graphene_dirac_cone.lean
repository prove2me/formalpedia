-- Prove2me | Theorems.Thm_GrapheneTightBinding_graphene_dirac_cone
-- name    : GrapheneTightBinding.graphene_dirac_cone
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:29:34.998476+00:00
-- url     : https://prove2.me/theorems/e057779c-16cc-49b6-8960-ad51f7e75b9d
-- title:
--   Graphene's Dirac cone: $E_\pm(k)=\pm t|\Delta_k|$, $E_+(K)=0$, $E_+(K+q)=v_F|q|+o(|q|)$
-- statement:
--   **Goal: the Dirac cone of graphene.** Let $a>0$ be the carbon–carbon distance and $t>0$
--   the nearest-neighbour hopping amplitude, and let
--   $$h(k)=-t\begin{pmatrix}0&\Delta_k\\ \overline{\Delta_k}&0\end{pmatrix},\qquad
--   \Delta_k=\sum_{j=1}^{3}e^{ik\cdot\delta_j},\qquad E_+(k)=t|\Delta_k| .$$
--   Then three things hold:
--
--   1. **Two bands $\pm E_+$.** For every wave vector $k$, the characteristic polynomial of
--      $h(k)$ is $X^2-E_+(k)^2$; that is, the eigenvalues of the Bloch Hamiltonian are
--      exactly $\pm E_+(k)$.
--   2. **Gapless at the Dirac point.** $E_+(K)=0$ at $K=\frac{2\pi}{3\sqrt3a}(\sqrt3,1)$: the
--      two bands touch there.
--   3. **Conical dispersion.** As $q\to0$,
--      $$E_+(K+q)=v_F|q|+o(|q|),\qquad v_F=\frac{3at}{2},\quad |q|=\sqrt{q_x^2+q_y^2}.$$
--
--   Together these say that the nearest-neighbour tight-binding model of graphene is a
--   two-band semimetal whose bands meet at the Brillouin-zone corner $K$ and disperse
--   linearly and isotropically around it with slope $v_F$ — the Dirac cone, and the origin of
--   the massless-Dirac-fermion description of graphene's low-energy electrons.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem graphene_dirac_cone (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    (∀ k : ℝ × ℝ, (hMat a t k).charpoly = X ^ 2 - C ((bandEnergy a t k : ℂ) ^ 2)) ∧
      bandEnergy a t (diracK a) = 0 ∧
      (fun q : ℝ × ℝ => bandEnergy a t (diracK a + q) - fermiVel a t * euclidNorm q)
        =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  sorry

end GrapheneTightBinding
