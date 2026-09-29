-- Prove2me | Theorems.Thm_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
-- name    : MeromorphicAt.exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8b893e37-b4d7-5f24-9719-7e1af97daf6a
-- title:
--   A pole in a product forces a pole in some factor
-- statement:
--   Let $\Bbbk$ be a nontrivially normed field, let $\iota$ and $\kappa$ be types, let $s$ be a finite subset of $\iota$ and $t$ a finite subset of $\kappa$, let $f_i : \Bbbk \to \Bbbk$ for $i \in \iota$, let $p : \Bbbk \to \Bbbk$, let $h_j : \Bbbk \to \Bbbk$ for $j \in \kappa$, and let $x \in \Bbbk$. Assume that each $f_i$ with $i \in s$ is meromorphic at $x$; that $p$ is meromorphic at $x$ with $\operatorname{ord}_x(p) < 0$ in $\mathbb{Z} \cup \{\pm\infty\}$ (Mathlib's `meromorphicOrderAt`, which takes the value $\top$ exactly on germs vanishing near $x$, so the hypothesis forces $p$ to have a genuine pole); that each $h_j$ with $j \in t$ is analytic at $x$ and satisfies $h_j(x) \neq 0$; and that, for $z$ in a punctured neighbourhood of $x$ (eventually along the filter $\mathcal{N}[\ne] x$), one has $\prod_{i \in s} f_i(z) = p(z) \prod_{j \in t} h_j(z)$. Then there exists $i \in s$ with $\operatorname{ord}_x(f_i) < 0$, i.e. some factor on the left-hand side already has a pole at $x$.
--
--   Elementary pole bookkeeping for germs of meromorphic functions: additivity of the order of vanishing along finite products, combined with the fact that a unit at $x$ contributes order $0$. It is used in the analytic part of the argument about Hecke eigensystems, in [`AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.HeckeEigensystem.exists_pow_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable), to locate a pole of an individual Euler-type factor from a pole of a product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MeromorphicAt.exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι κ : Type*}
    {s : Finset ι} {t : Finset κ} {f : ι → 𝕜 → 𝕜} {p : 𝕜 → 𝕜} {h : κ → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : ∀ j ∈ t, AnalyticAt 𝕜 (h j) x) (hh0 : ∀ j ∈ t, h j x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * ∏ j ∈ t, h j z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by sorry
