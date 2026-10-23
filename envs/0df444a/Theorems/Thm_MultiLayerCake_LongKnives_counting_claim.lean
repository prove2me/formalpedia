-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_counting_claim
-- name    : MultiLayerCake.LongKnives.counting_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:01.882021+00:00
-- url     : https://prove2.me/theorems/56b4c8f1-41f7-4ffa-9ab1-13f48e4f15d9
-- title:
--   Proof of Theorem 1, p. 11 — the claim ⌊n/q⌋ ≤ |π⁻¹(j)| ≤ ⌈n/q⌉
-- statement:
--   Let $n=N+1$ and $q\ge1$, and let $\pi:[n]\to[q]$ be an assignment with $\pi(n)=j^*$ such that
--   $$|\pi^{-1}(j^*)|=\Big\lfloor\frac{n-1}{q}\Big\rfloor+1,\qquad |\pi^{-1}(j)|\in\Big\{\Big\lfloor\frac{n-1}{q}\Big\rfloor,\Big\lceil\frac{n-1}{q}\Big\rceil\Big\}\ (j\neq j^*)$$
--   (the conclusion of Lemma 4 for $a_j=(n-1)/q$). Then for every $j\in[q]$,
--   $$\Big\lfloor\frac nq\Big\rfloor\le|\pi^{-1}(j)|\le\Big\lceil\frac nq\Big\rceil .$$
--
--   This is the step of the proof of Theorem 1 converting the group sizes produced by Lemma 4, which count the $n-1$ non-birthday agents, into the sizes $\{\lfloor n/q\rfloor,\lceil n/q\rceil\}$ of Theorem 1, which count the birthday agent too.
--
--   **Formalization Note.** $\lfloor\cdot/q\rfloor$ is natural-number division and $\lceil n/q\rceil$ is `⌈(n : ℚ) / q⌉₊`. The hypothesis on $j\ne j^*$ follows the corrected reading of Lemma 4.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 11, Proof of Theorem 1 (claim ⌊n/q⌋ ⩽ |π^{-1}_{j∗}(j)| ⩽ ⌈n/q⌉)

import Mathlib

namespace MultiLayerCake.LongKnives

/-- Proof of Theorem 1, p. 11, the claim `⌊n/q⌋ ≤ |π⁻¹_{j∗}(j)| ≤ ⌈n/q⌉`: if an assignment
`π : [N + 1] → [q]` (`n = N + 1` agents, the last one the birthday agent) has `π(N) = j∗`,
`|π⁻¹(j∗)| = ⌊N/q⌋ + 1` and `|π⁻¹(j)| ∈ {⌊N/q⌋, ⌈N/q⌉}` for `j ≠ j∗` (Lemma 4 with
`a_j = (n − 1)/q`), then every fibre has size between `⌊n/q⌋` and `⌈n/q⌉`. -/
theorem counting_claim {N q : ℕ} (π : Fin (N + 1) → Fin q) (jStar : Fin q)
    (hb : π (Fin.last N) = jStar)
    (hstar : (Finset.univ.filter (fun i => π i = jStar)).card = N / q + 1)
    (hother : ∀ j, j ≠ jStar → N / q ≤ (Finset.univ.filter (fun i => π i = j)).card ∧
      (Finset.univ.filter (fun i => π i = j)).card ≤ ⌈(N : ℚ) / q⌉₊) :
    ∀ j, (N + 1) / q ≤ (Finset.univ.filter (fun i => π i = j)).card ∧
      (Finset.univ.filter (fun i => π i = j)).card ≤ ⌈((N + 1 : ℕ) : ℚ) / q⌉₊ := by sorry

end MultiLayerCake.LongKnives
