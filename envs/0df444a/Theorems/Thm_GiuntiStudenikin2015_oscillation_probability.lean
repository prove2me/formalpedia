-- Prove2me | Theorems.Thm_GiuntiStudenikin2015_oscillation_probability
-- name    : GiuntiStudenikin2015.oscillation_probability
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:11:05.707452+00:00
-- url     : https://prove2.me/theorems/5a75a660-63a3-43d4-add9-fa467a24d695
-- title:
--   General neutrino oscillation probability in vacuum, Eq. (2.37)
-- statement:
--   Let $n\ge1$ be the number of massive neutrinos, $U$ a unitary $n\times n$ mixing matrix (rows: flavors $\ell$; columns: massive states $k$), $m_1,\dots,m_n\in\mathbb R$ the neutrino masses with $\Delta m^2_{kj}=m_k^2-m_j^2$, $L\in\mathbb R$ the source–detector distance and $E>0$ the neutrino energy. Define the flavor transition probability by the plane-wave formula (2.35) with the ultrarelativistic phases (2.36),
--   $$P_{\nu_\ell\to\nu_{\ell'}}(L,E)=\Bigl|\sum_k U^*_{\ell k}\,e^{-i m_k^2L/(2E)}\,U_{\ell' k}\Bigr|^2 .$$
--   Then for all flavors $\ell,\ell'$
--   $$P_{\nu_\ell\to\nu_{\ell'}}(L,E)=\delta_{\ell\ell'}-4\sum_{k>j}\operatorname{Re}\bigl(U^*_{\ell k}U_{\ell' k}U_{\ell j}U^*_{\ell' j}\bigr)\sin^2\!\Bigl(\frac{\Delta m^2_{kj}L}{4E}\Bigr)-2\sum_{k>j}\operatorname{Im}\bigl(U_{\ell k}U^*_{\ell j}U^*_{\ell' k}U_{\ell' j}\bigr)\sin\!\Bigl(\frac{\Delta m^2_{kj}L}{2E}\Bigr).$$
--
--   This is the general formula for neutrino flavor transitions in vacuum used throughout oscillation phenomenology; the second sum is the CP-violating part.
--
--   **Formalization Note** The number $n$ of massive states is arbitrary (the paper's case is $n=3$); unitarity is membership in `Matrix.unitaryGroup`, i.e. $UU^\dagger=U^\dagger U=1$.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531, pp. 535–536, Sec. II.D, Eqs. (2.30)–(2.37)

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

namespace GiuntiStudenikin2015
theorem oscillation_probability {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (m : Fin n → ℝ) (L E : ℝ) (hE : 0 < E)
    (l l' : Fin n) :
    oscProb U m L E l l' =
      (if l = l' then 1 else 0)
      - 4 * ∑ k : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < k),
          (star (U l k) * U l' k * U l j * star (U l' j)).re *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (4 * E)) ^ 2
      - 2 * ∑ k : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j < k),
          (U l k * star (U l j) * star (U l' k) * U l' j).im *
            Real.sin ((m k ^ 2 - m j ^ 2) * L / (2 * E)) := by sorry
end GiuntiStudenikin2015
