-- Prove2me | Theorems.Thm_NumberField_nonempty_algHom_cyclotomicField_of_dvd
-- name    : NumberField.nonempty_algHom_cyclotomicField_of_dvd
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:48:31.259488+00:00
-- url     : https://prove2.me/theorems/51005934-4456-45d2-b0a8-dccdfbeaaf84
-- title:
--   $\mathbb{Q}(\zeta_m)$ embeds in $\mathbb{Q}(\zeta_k)$ when $m \mid k$
-- statement:
--   Let $m, k \ge 1$ be integers with $m \mid k$. Then there is an embedding of $\mathbb{Q}$-algebras
--   $$\mathbb{Q}(\zeta_m) \hookrightarrow \mathbb{Q}(\zeta_k).$$
--
--   Indeed, if $\zeta$ is a primitive $k$-th root of unity in $\mathbb{Q}(\zeta_k)$, then $\zeta^{k/m}$ is a primitive $m$-th root of unity, so the $m$-th cyclotomic polynomial splits in $\mathbb{Q}(\zeta_k)$, and $\mathbb{Q}(\zeta_m)$, being its splitting field, embeds.
--
--   **Formalization note.** $\mathbb{Q}(\zeta_n)$ is Mathlib's `CyclotomicField n ℚ` (the splitting field of the $n$-th cyclotomic polynomial over $\mathbb{Q}$).
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 2 (Q(zeta_m) is a subfield of Q(zeta_k) when m | k; cf. Exercise 2.3 and the proof of Theorem 14.1).

import Mathlib.NumberTheory.Cyclotomic.Basic

theorem NumberField.nonempty_algHom_cyclotomicField_of_dvd {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hdvd : m ∣ k) : Nonempty (CyclotomicField m ℚ →ₐ[ℚ] CyclotomicField k ℚ) := by sorry
