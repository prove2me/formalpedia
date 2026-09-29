-- Prove2me | Theorems.Thm_ModularCurve_ssJSet_finite
-- name    : ModularCurve.ssJSet_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/c8a09641-0453-52b3-8dda-471400239c0e
-- title:
--   Finiteness of the supersingular j-invariants
-- statement:
--   Let $q$ be a prime and let $K$ be an algebraically closed field of characteristic $q$ (with decidable equality). Consider the set $\mathrm{ssJSet}\,q\,K \subseteq K$ consisting of those $j \in K$ with the property that for every Weierstrass curve $W$ over $K$ which is elliptic (invertible discriminant) and whose $j$-invariant equals $j$, every point $P$ of the associated affine curve $W.\mathrm{toAffine}$ killed by $q$, that is with $q \cdot P = 0$ for the natural-number scalar action on the group of points, is already the point at infinity $P = 0$; equivalently, no elliptic curve over $K$ with that $j$-invariant has a nontrivial $K$-rational $q$-torsion point. The assertion is that this subset of $K$ is finite. Since $K$ is algebraically closed, every $j \in K$ is realised by an elliptic curve, so the condition is the usual supersingularity of the curves with invariant $j$; note that the defining condition quantifies over all elliptic Weierstrass models with the given $j$-invariant, not over one chosen model.
--
--   This is the classical finiteness of the set of supersingular $j$-invariants in characteristic $q$ (in fact they all lie in $\mathbb{F}_{q^2}$ and number roughly $q/12$). It is used downstream in the analysis of the special fibre at $q$ of the modular curve, where the supersingular points form the finite set of singular points of the Deligne–Rapoport model and index the character group of the toric part of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssJSet_finite.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem ssJSet_finite (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ssJSet q K).Finite := by sorry
