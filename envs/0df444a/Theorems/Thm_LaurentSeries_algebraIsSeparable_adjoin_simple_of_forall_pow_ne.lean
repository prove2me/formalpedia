-- Prove2me | Theorems.Thm_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne
-- name    : LaurentSeries.algebraIsSeparable_adjoin_simple_of_forall_pow_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c168e70c-f26e-5282-9a2d-4bfce6be0fe3
-- title:
--   Separability of finite extensions of k(t) inside k((q))
-- statement:
--   Let $p$ be a prime, and let $k$ be a field of characteristic $p$ which is perfect (in the sense that the $p$-power endomorphism of $k$ is bijective). Inside the field $k(\!(q)\!)$ of formal Laurent series over $k$, let $F$ be an intermediate field of the extension $k(\!(q)\!)/k$, and let $t$ be an element of $F$. Assume that $t$ is transcendental over $k$, and that no Laurent series $v \in k(\!(q)\!)$ satisfies $v^p = t$, i.e. $t$ is not a $p$-th power in $k(\!(q)\!)$. Let $k\langle t\rangle$ denote the subfield of $F$ generated over $k$ by $t$, and assume that $F$ is finite-dimensional as a vector space over $k\langle t\rangle$. The conclusion is that the extension $F/k\langle t\rangle$ is separable: every element of $F$ is separable over the rational function field $k(t)$ realised as $k\langle t\rangle \subseteq F$.
--
--   This is a purely field-theoretic separability criterion for finite extensions of a rational function field sitting inside a field of Laurent series in characteristic $p$, the point being that the derivation $d/dq$ on $k(\!(q)\!)$ has kernel exactly the $p$-th powers when $k$ is perfect, so a non-$p$-th-power transcendental $t$ has non-zero derivative. It is used in the construction of the function field of the modular curve $X_1$ in characteristic $p$ via $q$-expansions, where the $j$-invariant series plays the role of $t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped IntermediateField

theorem LaurentSeries.algebraIsSeparable_adjoin_simple_of_forall_pow_ne
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (F : IntermediateField k (LaurentSeries k)) (t : ↥F)
    (htr : Transcendental k t) (hp : ∀ v : LaurentSeries k, v ^ p ≠ (t : LaurentSeries k))
    [FiniteDimensional ↥k⟮t⟯ ↥F] :
    Algebra.IsSeparable ↥k⟮t⟯ ↥F := by sorry
