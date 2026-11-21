-- Prove2me | Theorems.Thm_MasulloRepair_inertia_groupoid_composition_corrected
-- name    : MasulloRepair.inertia_groupoid_composition_corrected
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:03.802696+00:00
-- url     : https://prove2.me/theorems/88a4e3ba-f754-4a34-954d-a11096fe2d1f
-- title:
--   Corrected composition law for the inertia groupoid of Lemma E.6.3.6: $c'((r,g),(r',g'))=(c(r,r'),g')$
-- statement:
--   **Setting.** Let $(X,R,s,t,c,e,i)$ be a groupoid in sets in the sense of Definition E.4.1.1 of the manuscript: $s,t:R\to X$, a composition $c(x,y)$ defined for $s(x)=t(y)$, a unit $e:X\to R$ and an inversion $i:R\to R$ with
--
--   - $t(c(x,y))=t(x)$, $s(c(x,y))=s(y)$ for composable $(x,y)$;
--   - $c(x,c(y,z))=c(c(x,y),z)$ whenever $s(x)=t(y)$ and $s(y)=t(z)$;
--   - $s(e(a))=t(e(a))=a$; $\;c(x,e(s(x)))=x=c(e(t(x)),x)$;
--   - $s(i(x))=t(x)$, $t(i(x))=s(x)$; $\;c(x,i(x))=e(t(x))$, $c(i(x),x)=e(s(x))$.
--
--   (In the formal statement $c:R\to R\to R$ is total and the axioms are imposed on composable pairs only.) Following Definition E.6.3.4 and Lemma E.6.3.6 (p. 925), let $I=\{g\in R:\ s(g)=t(g)\}$ be the inertia, $G'=R\times_{s,X}I=\{(r,g):\ s(r)=s(g)=t(g)\}$, $s'(r,g)=g$ and $t'(r,g)=c(r,c(g,i(r)))$ (that is, $r g r^{-1}$).
--
--   **Statement.** Let $(r,g),(r',g')\in G'$ with $s'(r,g)=t'(r',g')$, i.e. $g=c(r',c(g',i(r')))$. Then:
--
--   1. $s(r)=t(r')$, so $c(r,r')$ is defined;
--   2. the value printed in Lemma E.6.3.6(3), $(c(r,r'),g)$, lies in $G'$ **if and only if** $s(r')=t(r')$: formally $s(c(r,r'))=s(g)\iff s(r')=t(r')$;
--   3. the corrected value $(c(r,r'),g')$ lies in $G'$: $s(c(r,r'))=s(g')$ (and $g'\in I$ by hypothesis);
--   4. the corrected value has the right target:
--   $$t'\bigl(c(r,r'),g'\bigr)=c\bigl(c(r,r'),\,c(g',i(c(r,r')))\bigr)=c\bigl(r,c(g,i(r))\bigr)=t'(r,g).$$
--
--   Its source is $s'(c(r,r'),g')=g'=s'(r',g')$ by definition.
--
--   **Relation to the manuscript.** This is a corrected version of the composition law in item (3) of Lemma E.6.3.6 (p. 925), which is printed as $c'((r,g),(r',g')):=(c(r,r'),g)$. By (2) the printed formula leaves $G'$ whenever $r'$ is not a loop (a concrete instance is `MasulloAudit.inertia_groupoid_printed_composition_leaves_fibre_product`); by (1), (3), (4) the formula $c'((r,g),(r',g')):=(c(r,r'),g')$ is well defined on $G'\times_{s',I,t'}G'$ and compatible with $s'$ and $t'$, as required by axiom (1)(a) of Definition E.4.1.1. The theorem is purely set-theoretic; it does not address continuity, the remaining groupoid axioms for $(I,G',s',t',c')$, or the equivalence of stacks asserted in the second half of the lemma.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Lemma E.6.3.6, item (3), p. 925 (PDF p. 925); groupoid axioms from Definition E.4.1.1, pp. 883-884; inertia from Definition E.6.3.4, p. 925

import Mathlib.Logic.Basic
import Mathlib.Tactic.Common

theorem MasulloRepair.inertia_groupoid_composition_corrected
    {X R : Type*} (s t : R → X) (c : R → R → R) (e : X → R) (i : R → R)
    (hc : ∀ x y, s x = t y → t (c x y) = t x ∧ s (c x y) = s y)
    (hassoc : ∀ x y z, s x = t y → s y = t z → c x (c y z) = c (c x y) z)
    (he : ∀ a, s (e a) = a ∧ t (e a) = a)
    (hid : ∀ x, c x (e (s x)) = x ∧ c (e (t x)) x = x)
    (hi : ∀ x, s (i x) = t x ∧ t (i x) = s x)
    (hinv : ∀ x, c x (i x) = e (t x) ∧ c (i x) x = e (s x))
    (r g r' g' : R)
    (hg : s g = t g) (hr : s r = s g)
    (hg' : s g' = t g') (hr' : s r' = s g')
    (hgeq : g = c r' (c g' (i r'))) :
    s r = t r' ∧
    (s (c r r') = s g ↔ s r' = t r') ∧
    s (c r r') = s g' ∧
    c (c r r') (c g' (i (c r r'))) = c r (c g (i r)) := by sorry
