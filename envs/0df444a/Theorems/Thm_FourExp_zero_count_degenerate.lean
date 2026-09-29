-- Prove2me | Theorems.Thm_FourExp_zero_count_degenerate
-- name    : FourExp.zero_count_degenerate
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T03:45:31.556807+00:00
-- url     : https://prove2.me/theorems/e7bb8de6-eb16-421c-a71b-a457db838e41
-- title:
--   Zeros of an exponential polynomial in the degenerate cases
-- statement:
--   **Degenerate cases of the zero count.**
--
--   With $f$, $n$ and $\Omega$ as in `FourExp.expPoly_zero_count`, suppose $n \le 1$ or $\Omega = 0$. Then for every finite set $S$,
--   $$\sum_{z \in S} \operatorname{ord}_z f \;\le\; n - 1 .$$
--
--   **Proof idea.**
--   - If $n = 1$, then $f = b\,e^{\omega z}$ with $b \ne 0$, which has no zeros. The indices with $q_j = 0$ contribute nothing.
--   - If $\Omega = 0$, every $\omega_j$ is $0$. Since they are distinct there is a single index, so $f$ is a non-zero polynomial of degree less than $n$, with at most $n - 1$ zeros counted with multiplicity.
--
--   **What it is for.** With `FourExp.zero_count_arith_poly` it covers the cases of `FourExp.expPoly_zero_count` that the rescaling argument cannot handle.
-- source:
--   Elementary. The degenerate cases of M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, Lemma 3.

import Mathlib

open Finset

namespace FourExp

theorem zero_count_degenerate
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (S : Finset ℂ) (hdeg : (∑ j, q j) ≤ 1 ∨ (⨆ j, ‖ω j‖) = 0) :
    (∑ z ∈ S, analyticOrderNatAt (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z) + 1 ≤ ∑ j, q j := by
  sorry

end FourExp
