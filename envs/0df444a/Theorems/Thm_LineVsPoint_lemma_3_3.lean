-- Prove2me | Theorems.Thm_LineVsPoint_lemma_3_3
-- name    : LineVsPoint.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:35.500512+00:00
-- url     : https://prove2.me/theorems/3eef23dc-ceec-4dc2-ae8e-26c7337d5a4e
-- title:
--   Lemma 3.3 — the pruned graph is large, of minimum degree $k$, with simple roots
-- statement:
--   **Lemma 3.3.** The pruning process leaves a nonempty graph $G$, with point side $X$, line side $T$, and edge set $E$. It has minimum degree at least $k$ and $\mu(E)\ge\varepsilon/2$. Moreover:
--
--   1. for every $x\in X$, $A(x,f(x))=0$ and $A_Z(x,f(x))\ne0$;
--   2. for every $L\in T$, $A(L(t),p_L(t))\equiv0$.
--
--
--   The statement is in the context of Section 3 (p.15): $m=2$, $d\ge1$, $\mathrm{Acc}(f,\{P_L\})\ge\varepsilon\ge C(d/q)^{1/3}$ for a sufficiently large absolute constant $C$, $D=\lceil4(dq^2)^{1/3}\rceil$, $k=\lfloor\varepsilon q/1000\rfloor$; $A$ is any polynomial as in Lemma 3.2 (nonzero, squarefree, $\mathrm{wdeg}(A)\le D$, $A(x,f(x))=0$ for all $x$) and $\lambda$ any direction with $\gcd(A,S)=1$ for $S=\lambda_XA_X+\lambda_YA_Y+\lambda_ZA_Z$. The graph $G$ is obtained from the accepted incidences by the three deletions of Step 2 and repeated removal of vertices of degree below $k$; $X$, $T$, $E$ are its point side, line side and edge set, with $\mu(E)=|E|/(q^2(q+1))$, $\mu(X')=|X'|/q^2$ and $\mu(T')=|T'|/(q(q+1))$.
--
--   The lemma provides the graph on which the bivariate argument propagates a single polynomial.
--
--   Differences from the source:
--   - encoding: for a sufficiently large absolute constant C (Section 3 context, p.15) → ∃ C > 0 before the field and every other variable; reason: the hypothesis C(d/q)^{1/3} ≤ ε only strengthens as C grows, so a statement for one C gives it for every larger C
--   - encoding: A fixed from Lemma 3.2 and λ chosen by Lemma 2.3 with gcd(A, S) = 1 → every A ≠ 0, squarefree, with wdeg(A) ≤ D and A(x, f(x)) = 0 for all x, and every λ with IsRelPrime A (D_λ A); reason: the statement must hold for whichever admissible A and λ the proof picks
--   - reading: the graph left by the three deletions after repeatedly removing vertices of degree below k → the k-core: the union of all vertex sets in which every vertex has at least k surviving neighbours (prunedGraph); reason: repeated removal ends at the largest such set whatever the order of removals
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 3.3, p.16 (context §3, p.15)

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_dirDeriv
import Definitions.Def_LineVsPoint_sec3D
import Definitions.Def_LineVsPoint_prunedGraph

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
open Classical in
/-- **Lemma 3.3** (the pruned graph). *The pruning process leaves a nonempty graph `G`, with point
side `X`, line side `T`, and edge set `E`. It has minimum degree at least `k` and `µ(E) ≥ ε/2`.
Moreover: (i) for every `x ∈ X`, `A(x, f(x)) = 0`, `A_Z(x, f(x)) ≠ 0`; (ii) for every `L ∈ T`,
`A(L(t), p_L(t)) ≡ 0`.* Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the
Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 3.3, p.16, in the Section 3
context of p.15.

**Formalization Note.** The Section 3 context (p.15): `m = 2`, `Acc(f, {P_L}) ≥ ε ≥ C(d/q)^{1/3}`
for a sufficiently large absolute `C` (here `∃ C` before everything, which is equivalent because
the hypothesis only strengthens as `C` grows), `D = ⌈4(dq²)^{1/3}⌉`, `k = ⌊εq/1000⌋`. `A` is any
polynomial as in Lemma 3.2 and `λ` any direction with `gcd(A, S) = 1` for
`S = λ_X A_X + λ_Y A_Y + λ_Z A_Z` (`IsRelPrime`); the statement holds for every such choice. `G`
is `prunedGraph`: the three deletions of p.15 followed by the `k`-core. Its point side is
`{x | inl x ∈ kCore}`, line side `{L | inr L ∈ kCore}`, edge set `prunedEdges`, and
`µ(E) = |E|/(q²(q+1))` (§2.2, p.10). -/
theorem lemma_3_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] (d : ℕ), 1 ≤ d →
      ∀ (f : (Fin 2 → F) → F) (P : LineTable F 2 d) (ε : ℝ), ε ≤ acc f P →
      C * ((d : ℝ) / (Fintype.card F : ℝ)) ^ (1 / 3 : ℝ) ≤ ε →
      ∀ A : MvPolynomial (Fin 3) F, A ≠ 0 → Squarefree A →
      weightedTotalDegree ![1, 1, d] A ≤ sec3D d (Fintype.card F) →
      (∀ x : Fin 2 → F, eval ![x 0, x 1, f x] A = 0) →
      ∀ lam : Fin 3 → F, IsRelPrime A (dirDeriv lam A) →
        (kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Nonempty ∧
        (∀ v ∈ kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F)),
          sec3k ε (Fintype.card F) ≤ (Finset.univ.filter fun w =>
            (prunedGraph f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).Adj v w).card) ∧
        ε / 2 ≤ ((prunedEdges f P A (dirDeriv lam A) (sec3k ε (Fintype.card F))).card : ℝ) /
          ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) + 1)) ∧
        (∀ x : Fin 2 → F,
          Sum.inl x ∈ kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F)) →
          eval ![x 0, x 1, f x] A = 0 ∧ eval ![x 0, x 1, f x] (pderiv 2 A) ≠ 0) ∧
        (∀ L : Line F 2,
          Sum.inr L ∈ kCore f P A (dirDeriv lam A) (sec3k ε (Fintype.card F)) →
          graphRestrict (P.a L) (P.u L) (P.p L) A = 0) := by sorry

end LineVsPoint
