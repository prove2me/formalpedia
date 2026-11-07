-- Prove2me | Theorems.Thm_LineVsPoint_lemma_3_4
-- name    : LineVsPoint.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:39.097764+00:00
-- url     : https://prove2.me/theorems/a7224afc-3a2e-44a1-8293-bf53cd607259
-- title:
--   Lemma 3.4 — every connected component of $G$ has density at least $k/(4q)$
-- statement:
--   **Lemma 3.4.** Let $(X',T')$ be the point and line sides of a connected component of $G$. Then
--
--   $$
--   \mu(X'),\ \mu(T')\ \ge\ \frac{k}{4q}\ \ge\ \frac{\varepsilon}{8000}.
--   $$
--
--
--   The statement is in the context of Section 3 (p.15): $m=2$, $d\ge1$, $\mathrm{Acc}(f,\{P_L\})\ge\varepsilon\ge C(d/q)^{1/3}$ for a sufficiently large absolute constant $C$, $D=\lceil4(dq^2)^{1/3}\rceil$, $k=\lfloor\varepsilon q/1000\rfloor$; $A$ is any polynomial as in Lemma 3.2 (nonzero, squarefree, $\mathrm{wdeg}(A)\le D$, $A(x,f(x))=0$ for all $x$) and $\lambda$ any direction with $\gcd(A,S)=1$ for $S=\lambda_XA_X+\lambda_YA_Y+\lambda_ZA_Z$. The graph $G$ is obtained from the accepted incidences by the three deletions of Step 2 and repeated removal of vertices of degree below $k$; $X$, $T$, $E$ are its point side, line side and edge set, with $\mu(E)=|E|/(q^2(q+1))$, $\mu(X')=|X'|/q^2$ and $\mu(T')=|T'|/(q(q+1))$.
--
--   Combined with Lemma 3.5, a single component already yields a polynomial agreeing with $f$ on an $\varepsilon/8000$ fraction of points.
--
--   Differences from the source:
--   - encoding: for a sufficiently large absolute constant C (Section 3 context, p.15) → ∃ C > 0 before the field and every other variable; reason: the hypothesis C(d/q)^{1/3} ≤ ε only strengthens as C grows, so a statement for one C gives it for every larger C
--   - encoding: A fixed from Lemma 3.2 and λ chosen by Lemma 2.3 with gcd(A, S) = 1 → every A ≠ 0, squarefree, with wdeg(A) ≤ D and A(x, f(x)) = 0 for all x, and every λ with IsRelPrime A (D_λ A); reason: the statement must hold for whichever admissible A and λ the proof picks
--   - reading: the graph left by the three deletions after repeatedly removing vertices of degree below k → the k-core: the union of all vertex sets in which every vertex has at least k surviving neighbours (prunedGraph); reason: repeated removal ends at the largest such set whatever the order of removals
--   - encoding: a connected component (X′, T′) of G → a vertex v of G (an element of the k-core), with X′ = {x | v ⇝ inl x} and T′ = {L | v ⇝ inr L} by reachability in prunedGraph; reason: the components of G are the reachability classes of its vertices
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 3.4, p.16 (context §3, p.15)

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_dirDeriv
import Definitions.Def_LineVsPoint_sec3D
import Definitions.Def_LineVsPoint_prunedGraph

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
open Classical in
/-- **Lemma 3.4** (components are large). *Let `(X′, T′)` be the point and line sides of a
connected component of `G`. Then `µ(X′), µ(T′) ≥ k/(4q) ≥ ε/8000`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 3.4, p.16, in the Section 3 context of p.15.

**Formalization Note.** Same context and graph as `lemma_3_3`. A connected component of `G` is
given by a vertex `v` of `G` (an element of the `k`-core): `X′ = {x | v ⇝ inl x}` and
`T′ = {L | v ⇝ inr L}` (reachability in `G`). `µ(X′) = |X′|/q²` and `µ(T′) = |T′|/(q(q+1))`
(§2.2, p.10). All three inequalities are asserted. -/
theorem lemma_3_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] (d : ℕ), 1 ≤ d →
      ∀ (f : (Fin 2 → F) → F) (P : LineTable F 2 d) (ε : ℝ), ε ≤ acc f P →
      C * ((d : ℝ) / (Fintype.card F : ℝ)) ^ (1 / 3 : ℝ) ≤ ε →
      ∀ A : MvPolynomial (Fin 3) F, A ≠ 0 → Squarefree A →
      weightedTotalDegree ![1, 1, d] A ≤ sec3D d (Fintype.card F) →
      (∀ x : Fin 2 → F, eval ![x 0, x 1, f x] A = 0) →
      ∀ lam : Fin 3 → F, IsRelPrime A (dirDeriv lam A) →
      ∀ v ∈ kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F)),
        (sec3k ε (Fintype.card F) : ℝ) / (4 * (Fintype.card F : ℝ)) ≤
            ((Finset.univ.filter fun x : Fin 2 → F =>
              (prunedGraph f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Reachable v
                (Sum.inl x)).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ∧
          (sec3k ε (Fintype.card F) : ℝ) / (4 * (Fintype.card F : ℝ)) ≤
            ((Finset.univ.filter fun L : Line F 2 =>
              (prunedGraph f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Reachable v
                (Sum.inr L)).card : ℝ) / ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1)) ∧
          ε / 8000 ≤ (sec3k ε (Fintype.card F) : ℝ) / (4 * (Fintype.card F : ℝ)) := by sorry

end LineVsPoint
