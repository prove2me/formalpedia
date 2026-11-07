-- Prove2me | Theorems.Thm_LineVsPoint_lemma_3_5
-- name    : LineVsPoint.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:15.018647+00:00
-- url     : https://prove2.me/theorems/77dfd2cf-a004-4cac-a77e-957780da78b6
-- title:
--   Lemma 3.5 — one polynomial of degree $d$ explains a whole component
-- statement:
--   **Lemma 3.5.** For every connected component $(X',T')$ of $G$ there is a polynomial $Q\in\mathbb F_q[X,Y]$ of total degree at most $d$ such that $Q(x)=f(x)$ for all $x\in X'$ and $Q|_L=P_L$ for all $L\in T'$.
--
--
--   The statement is in the context of Section 3 (p.15): $m=2$, $d\ge1$, $\mathrm{Acc}(f,\{P_L\})\ge\varepsilon\ge C(d/q)^{1/3}$ for a sufficiently large absolute constant $C$, $D=\lceil4(dq^2)^{1/3}\rceil$, $k=\lfloor\varepsilon q/1000\rfloor$; $A$ is any polynomial as in Lemma 3.2 (nonzero, squarefree, $\mathrm{wdeg}(A)\le D$, $A(x,f(x))=0$ for all $x$) and $\lambda$ any direction with $\gcd(A,S)=1$ for $S=\lambda_XA_X+\lambda_YA_Y+\lambda_ZA_Z$. The graph $G$ is obtained from the accepted incidences by the three deletions of Step 2 and repeated removal of vertices of degree below $k$; $X$, $T$, $E$ are its point side, line side and edge set, with $\mu(E)=|E|/(q^2(q+1))$, $\mu(X')=|X'|/q^2$ and $\mu(T')=|T'|/(q(q+1))$.
--
--   With Lemma 3.4 this proves the bivariate case of Theorem 3.1 with $c=1/8000$.
--
--   Differences from the source:
--   - encoding: for a sufficiently large absolute constant C (Section 3 context, p.15) → ∃ C > 0 before the field and every other variable; reason: the hypothesis C(d/q)^{1/3} ≤ ε only strengthens as C grows, so a statement for one C gives it for every larger C
--   - encoding: A fixed from Lemma 3.2 and λ chosen by Lemma 2.3 with gcd(A, S) = 1 → every A ≠ 0, squarefree, with wdeg(A) ≤ D and A(x, f(x)) = 0 for all x, and every λ with IsRelPrime A (D_λ A); reason: the statement must hold for whichever admissible A and λ the proof picks
--   - reading: the graph left by the three deletions after repeatedly removing vertices of degree below k → the k-core: the union of all vertex sets in which every vertex has at least k surviving neighbours (prunedGraph); reason: repeated removal ends at the largest such set whatever the order of removals
--   - encoding: a connected component (X′, T′) of G → a vertex v of G (an element of the k-core), with X′ = {x | v ⇝ inl x} and T′ = {L | v ⇝ inr L} by reachability in prunedGraph; reason: the components of G are the reachability classes of its vertices
--   - reading: Q|_L = P_L → the formal identity Q(a_L + t u_L) = p_L(t) in F[t]; reason: §2.1: identities refer to formal polynomials; the proof derives the formal identity (Lemma 2.6 uniqueness); for d < q it coincides with equality of functions on L
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 3.5, p.16 (context §3, p.15)

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_dirDeriv
import Definitions.Def_LineVsPoint_sec3D
import Definitions.Def_LineVsPoint_prunedGraph

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
/-- **Lemma 3.5** (one polynomial per component). *For every connected component `(X′, T′)` of
`G`, there is a polynomial `Q ∈ F_q[X, Y]` of total degree at most `d` such that `Q(x) = f(x)` for
all `x ∈ X′` and `Q|_L = P_L` for all `L ∈ T′`.* Dao, Kominers, Thaler, Zheng, *Cube-Root
Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 3.5,
p.16, in the Section 3 context of p.15.

**Formalization Note.** Same context, graph and components as `lemma_3_4`. `Q|_L = P_L` is the
formal identity `Q(a_L + t u_L) = p_L(t)` in `F[t]`. -/
theorem lemma_3_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] (d : ℕ), 1 ≤ d →
      ∀ (f : (Fin 2 → F) → F) (P : LineTable F 2 d) (ε : ℝ), ε ≤ acc f P →
      C * ((d : ℝ) / (Fintype.card F : ℝ)) ^ (1 / 3 : ℝ) ≤ ε →
      ∀ A : MvPolynomial (Fin 3) F, A ≠ 0 → Squarefree A →
      weightedTotalDegree ![1, 1, d] A ≤ sec3D d (Fintype.card F) →
      (∀ x : Fin 2 → F, eval ![x 0, x 1, f x] A = 0) →
      ∀ lam : Fin 3 → F, IsRelPrime A (dirDeriv lam A) →
      ∀ v ∈ kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F)),
        ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ d ∧
          (∀ x : Fin 2 → F,
            (prunedGraph f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Reachable v
              (Sum.inl x) → eval x Q = f x) ∧
          (∀ L : Line F 2,
            (prunedGraph f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Reachable v
              (Sum.inr L) → lineRestrict (P.a L) (P.u L) Q = P.p L) := by sorry

end LineVsPoint
