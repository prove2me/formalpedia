-- Prove2me | Theorems.Thm_GrapheneTightBinding_hMat_charpoly
-- name    : GrapheneTightBinding.hMat_charpoly
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T20:09:17.529975+00:00
-- url     : https://prove2.me/theorems/a6edacfa-abe6-4c8f-a321-91a91481dfab
-- title:
--   Eq. (9): the characteristic polynomial of $h(k)$ is $X^2-t^2|\Delta_k|^2$
-- statement:
--   **Spectrum of the Bloch Hamiltonian (Eq. 9).** For all real $a,t$ and every wave vector
--   $k$, the characteristic polynomial of the $2\times2$ Bloch Hamiltonian is
--   $$\chi_{h(k)}(X) \;=\; X^2-t^2\,\Delta_k\overline{\Delta_k}\;=\;X^2-t^2|\Delta_k|^2 .$$
--   Equivalently, $h(k)$ is traceless with determinant $-t^2|\Delta_k|^2$, so its two
--   eigenvalues are $E_\pm(k)=\pm t|\Delta_k|$: the two bands of the model.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem hMat_charpoly (a t : ℝ) (k : ℝ × ℝ) :
    (hMat a t k).charpoly =
      X ^ 2 - C ((t : ℂ) ^ 2 * (Delta a k * (starRingEnd ℂ) (Delta a k))) := by
  sorry

end GrapheneTightBinding
