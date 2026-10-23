-- Prove2me | Theorems.Thm_GTAlternating_Bases_lemma_2
-- name    : GTAlternating.Bases.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:07.325877+00:00
-- url     : https://prove2.me/theorems/d9389484-303e-4bcb-aaf0-0ae95e2a25c8
-- title:
--   Lemma 2, p. 6 — every associator φ_λ : V_λ → V_λ′ maps v_T to a multiple of v_{T′}
-- statement:
--   Let $\lambda$ be a partition of $n$ with conjugate $\lambda'$, and let $\varphi : V_\lambda \to V_{\lambda'}$ be a linear isomorphism satisfying the anticommutation relations (5),
--   $$\rho_{\lambda'}(s_i)\,\varphi + \varphi\,\rho_\lambda(s_i) = 0 \qquad (1 \le i \le n-1).$$
--   Then for every standard tableau $T$ of shape $\lambda$ there is a scalar $c_T$ with
--   $$\varphi(v_T) = c_T\, v_{T'},$$
--   where $T'$ is the conjugate tableau (the reflection of $T$ about its principal diagonal).
--
--   Such a $\varphi$ is an associator: an $S_n$-isomorphism $\epsilon \otimes \rho_\lambda \to \rho_{\lambda'}$. The lemma reduces its computation to the scalars $c_T$.
--
--   **Formalization Note.** `lam` is $\lambda$; `lam.transpose` is $\lambda'$; $\rho_\lambda(s_{i+1})$ is `sigma lam i` (0-based labels). `conjInto lam.transpose T` is $v_{T'}$.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 6, Lemma 2 (with (5), p. 6)

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem lemma_2 (lam : YoungDiagram) (f : V lam →ₗ[ℂ] V lam.transpose) (hf : Function.Bijective f)
    (h5 : ∀ i, i + 1 < lam.cells.card → sigma lam.transpose i ∘ₗ f + f ∘ₗ sigma lam i = 0)
    (T : SYT lam) : ∃ c : ℂ, f (vT T) = c • conjInto lam.transpose T := by sorry

end GTAlternating.Bases
