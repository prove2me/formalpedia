-- Prove2me | Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
-- name    : ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/d2da18aa-77e3-55a9-afe0-3ecb9306ce6c
-- title:
--   Supersingular j-invariants base-change along algebraically closed extensions
-- statement:
--   Let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $K$ be an algebraically closed field equipped with a $k$-algebra structure (so that $K$ is an extension of $k$, the decidable-equality data being taken classically). For a field $F$ write $\mathrm{ssJSet}(p,F)$ for the set of those $j \in F$ with the property that every Weierstrass curve $W$ over $F$ which is elliptic and satisfies $W.j = j$ has the feature that each point $P$ of the associated affine curve with $p \cdot P = 0$ is already $0$; that is, no elliptic Weierstrass model with $j$-invariant $j$ has a nontrivial $p$-torsion point. The assertion is the equality of subsets of $K$
--   $$\mathrm{ssJSet}(p,K) \;=\; \operatorname{algebraMap}_{k\to K}\bigl(\mathrm{ssJSet}(p,k)\bigr),$$
--   i.e. the supersingular $j$-invariants over $K$ are exactly the images of the supersingular $j$-invariants over $k$. In particular every supersingular $j$-invariant over $K$ already lies in the subfield $k$.
--
--   This is Deuring's observation that supersingularity in characteristic $p$ is insensitive to enlarging an algebraically closed base field, the supersingular $j$-invariants being the roots of a polynomial with coefficients in $\mathbb{F}_p$ (in fact they lie in $\mathbb{F}_{p^2}$). It is used to identify the supersingular points of a modular curve over a large algebraically closed field with those over $\overline{\mathbb{F}}_p$, for instance when base-changing differentials with poles supported at supersingular places; the proof cites the identification of $\mathrm{ssJSet}$ with the Hasse-invariant description and the description of the latter as the image under the Legendre $j$-map of the roots of the Deuring polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K] :
    @ssJSet p K _ (Classical.decEq K) = algebraMap k K '' @ssJSet p k _ (Classical.decEq k) := by sorry
