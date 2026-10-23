-- Prove2me | Theorems.Thm_GTAlternating_Bases_associator_eq_9
-- name    : GTAlternating.Bases.associator_eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:10.550978+00:00
-- url     : https://prove2.me/theorems/009c805c-bd45-4d6c-b032-4001a2958ebb
-- title:
--   §3, pp. 7–9, (7)–(9) — for any T_λ and c_{T_λ}, c_T = c_{T_λ}ϵ(w_T) gives (5); the self-conjugate φ_λ of (9) satisfies (5) and φ_λ² = id
-- statement:
--   Let $\lambda$ be a partition of $n$ with conjugate $\lambda'$. Fix any standard tableau $T_0$ of shape $\lambda$ and any scalar $c_0 \in \mathbb C$; for a standard tableau $T$ of shape $\lambda$ let $w_T$ be the permutation taking each entry of $T_0$ to the entry of $T$ in the same box, and let $\varphi : V_\lambda \to V_{\lambda'}$ be the linear map with
--   $$\varphi(v_T) = c_0\,\epsilon(w_T)\,v_{T'} \qquad (7).$$
--   Then $\varphi$ satisfies (5):
--   $$\rho_{\lambda'}(s_i)\,\varphi + \varphi\,\rho_\lambda(s_i) = 0 \qquad (1 \le i \le n-1).$$
--   Moreover, if $\lambda$ is self-conjugate, the associator $\varphi_\lambda$ fixed by (9), $\varphi_\lambda(v_T) = i^{(n-d(\lambda))/2}\,\epsilon(w_T)\,v_{T'}$ with $T_\lambda$ chosen as on pp. 8–9, satisfies (5) and
--   $$\varphi_\lambda^2 = \mathrm{id}_{V_\lambda},$$
--   which realises the paper's "one may additionally require $\varphi_\lambda^2 = \mathrm{id}$".
--
--   This is what makes $V_\lambda^{+}$ and $V_\lambda^{-}$ (the $\pm1$ eigenspaces of $\varphi_\lambda$) complementary $A_n$-invariant subspaces of $V_\lambda$.
--
--   **Formalization Note.** `assocRel T0 c0` is the map (7) for the reference tableau `T0` and $c_{T_\lambda} = $ `c0`; `signWRel T0 T` is $\epsilon(w_T)$ computed as $(-1)^{\#\text{inversions}}$. The case $c_0 = 0$ (the zero map) is allowed, as the page fixes $c_{T_\lambda}$ "arbitrarily". The second clause is stated for the specific normalisation (9) used in the rest of the paper. `sigma lam i` is $\rho_\lambda(s_{i+1})$ (0-based labels); multiplication of endomorphisms is composition.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, pp. 7–9, §3, (7) and the following paragraph, with (9) p. 9

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem associator_eq_9 (lam : YoungDiagram) :
    (∀ (T0 : SYT lam) (c0 : ℂ) (i : ℕ), i + 1 < lam.cells.card →
      sigma lam.transpose i ∘ₗ assocRel T0 c0 + assocRel T0 c0 ∘ₗ sigma lam i = 0) ∧
    (lam.transpose = lam →
      (∀ i, i + 1 < lam.cells.card → sigma lam i * phi lam + phi lam * sigma lam i = 0) ∧
        phi lam * phi lam = 1) := by sorry

end GTAlternating.Bases
