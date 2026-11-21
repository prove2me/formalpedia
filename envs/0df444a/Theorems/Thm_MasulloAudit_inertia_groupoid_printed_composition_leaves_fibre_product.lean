-- Prove2me | Theorems.Thm_MasulloAudit_inertia_groupoid_printed_composition_leaves_fibre_product
-- name    : MasulloAudit.inertia_groupoid_printed_composition_leaves_fibre_product
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:17:04.132184+00:00
-- url     : https://prove2.me/theorems/05afaa5a-73ce-43d9-bdc8-14c690caed5e
-- title:
--   The composition law printed in Lemma E.6.3.6(3), $c'((r,g),(r',g'))=(c(r,r'),g)$, does not land in $G'=G\times_{s,X}I$
-- statement:
--   **Setting.** A *groupoid in sets* in the sense of Definition E.4.1.1 of the manuscript is a tuple $(X,R,s,t,c,e,i)$: sets $X$ (objects) and $R$ (morphisms), maps $s,t:R\to X$, a composition $c:R\times_{s,X,t}R\to R$ defined on the pairs $(x,y)$ with $s(x)=t(y)$, a unit $e:X\to R$ and an inversion $i:R\to R$, such that
--
--   - $t(c(x,y))=t(x)$ and $s(c(x,y))=s(y)$ for composable $(x,y)$;
--   - $c(x,c(y,z))=c(c(x,y),z)$ whenever $s(x)=t(y)$ and $s(y)=t(z)$;
--   - $s(e(a))=t(e(a))=a$;
--   - $c(x,e(s(x)))=x=c(e(t(x)),x)$;
--   - $s(i(x))=t(x)$, $t(i(x))=s(x)$;
--   - $c(x,i(x))=e(t(x))$ and $c(i(x),x)=e(s(x))$.
--
--   In the formal statement $c$ is a total function $R\to R\to R$ and the axioms are imposed on composable pairs only, which is the same data as a function on the fibre product.
--
--   For a topological groupoid $(X,G,s,t,c,e,i)$, Definition E.6.3.4 puts $I:=I_{[G\rightrightarrows X]}=X\times_{\Delta,X\times X,(s,t)}G=\{g\in G:\ s(g)=t(g)\}$, and Lemma E.6.3.6 (p. 925) sets
--
--   $$G':=G\times_{s,X}I=\{(r,g):\ s(r)=s(g)=t(g)\},\qquad s'(r,g):=g,\qquad t'(r,g):=c(r,c(g,i(r))),$$
--
--   $$c':G'\times_{s',I,t'}G'\to G',\qquad c'\bigl((r,g),(r',g')\bigr):=(c(r,r'),\,g),$$
--
--   and asserts that $(I,G',s',t',c')$, with the uniquely determined unit and inverse, is a topological groupoid.
--
--   **Statement.** There is a groupoid in sets (the pair groupoid on a two-point set: $X=\{0,1\}$, $R=X\times X$, $s(a,b)=a$, $t(a,b)=b$, $c((b,d),(a,b))=(a,d)$, $e(a)=(a,a)$, $i(a,b)=(b,a)$; with the discrete topologies it is a topological groupoid) and elements $r,g,r',g'\in R$ such that
--
--   - $(r,g)\in G'$ and $(r',g')\in G'$, i.e. $s(g)=t(g)$, $s(r)=s(g)$, $s(g')=t(g')$, $s(r')=s(g')$;
--   - the pair is composable in the printed sense, $s'(r,g)=t'(r',g')$, i.e. $g=c(r',c(g',i(r')))$;
--   - but $s(c(r,r'))\neq s(g)$, so the printed value $c'((r,g),(r',g'))=(c(r,r'),g)$ is **not an element of** $G'=G\times_{s,X}I$.
--
--   **Relation to the manuscript.** This refutes item (3) of Lemma E.6.3.6 as printed: the displayed formula does not define a map $G'\times_{s',I,t'}G'\to G'$, so $(I,G',s',t',c')$ with this $c'$ is not a groupoid. (Reading the fibre product with the opposite convention does not help: then $c(r,r')$ itself is not defined in general.) The slip is in the second component: the composite of $(r',g'):g'\to g$ followed by $(r,g):g\to t'(r,g)$ must have source $g'$, so the formula should read $(c(r,r'),g')$. The companion theorem `MasulloRepair.inertia_groupoid_composition_corrected` proves, for every groupoid in sets, that the printed value lies in $G'$ exactly when $s(r')=t(r')$ and that the corrected value $(c(r,r'),g')$ lies in $G'$ and has the right target. Nothing is claimed here about the rest of Lemma E.6.3.6 (the equivalence of stacks $\mathcal I_{[X/G]}=[I/G']$) or about any later use of it.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Lemma E.6.3.6, item (3), p. 925 (PDF p. 925); groupoid axioms from Definition E.4.1.1, pp. 883-884; inertia from Definition E.6.3.4, p. 925

import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Common

theorem MasulloAudit.inertia_groupoid_printed_composition_leaves_fibre_product :
    ∃ (s t : Bool × Bool → Bool) (c : Bool × Bool → Bool × Bool → Bool × Bool)
      (e : Bool → Bool × Bool) (i : Bool × Bool → Bool × Bool),
      (∀ x y, s x = t y → t (c x y) = t x ∧ s (c x y) = s y) ∧
      (∀ x y z, s x = t y → s y = t z → c x (c y z) = c (c x y) z) ∧
      (∀ a, s (e a) = a ∧ t (e a) = a) ∧
      (∀ x, c x (e (s x)) = x ∧ c (e (t x)) x = x) ∧
      (∀ x, s (i x) = t x ∧ t (i x) = s x) ∧
      (∀ x, c x (i x) = e (t x) ∧ c (i x) x = e (s x)) ∧
      ∃ r g r' g' : Bool × Bool,
        s g = t g ∧ s r = s g ∧
        s g' = t g' ∧ s r' = s g' ∧
        g = c r' (c g' (i r')) ∧
        s (c r r') ≠ s g := by sorry
