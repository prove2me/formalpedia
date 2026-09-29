-- Prove2me | Theorems.Thm_KServer_workFnU_duality_injective
-- name    : KServer.workFnU_duality_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T09:29:18.431372+00:00
-- url     : https://prove2.me/theorems/0eb0f3ec-f6d1-4624-bd4a-b1f2ccd89cef
-- title:
--   The duality property for proper configurations
-- statement:
--   Fix a metric space $M$, $k\ge1$ servers, an initial configuration $C_0$, a request sequence $\sigma$ and one further request $r$. Write $D(X)=\sum_i d(r,X_i)$, and call a configuration **proper** when it is injective and avoids $r$ — in the classical language, a $k$-element set not containing $r$.
--
--   **Statement.** Let $A$ be a proper configuration minimising $\widehat w_{t-1}(X)-D(X)$ **among proper configurations**. Then $A$ also minimises $\widehat w_t(X)-D(X)$ among proper configurations, and it maximises $\widehat w_t(X)-\widehat w_{t-1}(X)$ among **all injective** configurations.
--
--   **Status (updated).** The case $\#M = k+2$, which is the one the $(k+2)$-point argument needs, is settled: it is now a step inside the proof of [`workFnU_growth_card_add_two_inj`](p2m:theorem/c697f8e8-99c9-4066-b8f6-a0602e89d78b), and the milestone [`card_add_two_competitive`](p2m:theorem/642b0d4b-34e0-457c-b337-dc050ed5a72d) is proved. **What remains open here is the statement above for an arbitrary metric space**, which is strictly more than that argument gives.
--
--   **How the $k+2$ case goes, and why it does not generalise.** On a space with exactly $k+2$ points an injective configuration *is* the complement of a pair, so writing $W(u,v)=\widehat w(\{u,v\}^C)$ and
--   $$\mu(\{u,v\})=W(u,v)+d(r,u)+d(r,v)=\bigl[\widehat w-D\bigr]\bigl(\{u,v\}^C\bigr)+\sum_{x\in V}d(r,x),$$
--   the recurrence collapses to an edge recurrence $W'(r,b)+d(r,b)=\min_c \mu(\{b,c\})$ — the two-evader problem. Let $e^\*=\{A,C\}$ minimise $\mu$ over the edges missing $r$. For $b\notin e^\*\cup\{r\}$ the four points $r,b,A,C$ are distinct, and quasiconvexity applied to the two injective configurations $\{r,b\}^C$ and $(e^\*)^C$ yields one of the two exchanges
--   $$\mu(\{r,b\})+\mu(e^\*)\ \ge\ \mu(\{r,z\})+\mu(\{b,z'\}),\qquad\{z,z'\}=\{A,C\},$$
--   from which $W'(r,b)-W(r,b)\le W'(r,z)-W(r,z)$ follows in one line. The essential point — and the answer to the difficulty recorded below — is that for *these two* configurations the quasiconvexity hybrids can be kept **injective**: they differ in exactly two points, so choosing the hybrid index set to be the complement of a reachability set under "the point I contribute is the point the other configuration contributes here" makes both hybrids injective, misses $r$ from one and $b$ from the other, and keeps every commonly occupied point in both.
--
--   That repair uses $\#M=k+2$ twice: it needs the two configurations to differ in exactly two points, and it needs the counting step that forces exactly one of $A,C$ to be missing from the first hybrid. On a larger space two injective configurations can differ in up to $k$ points and the hybrids genuinely fail to be injective, so the general statement still needs a different idea.
--
--   **Why the unrestricted duality lemma does not suffice.** In this model a configuration is a labelled map $\{1,\dots,k\}\to M$, so it may place two servers on the same point, and `workFnU` extends the classical work function from $k$-element sets to multisets. Exact dynamic programming shows that the minimum of $\widehat w_{t-1}(X)-D(X)$ over *all* configurations is sometimes attained only at multisets with a repeat: on $(k+2)$-point spaces this happened at roughly 2% of steps for $k=2$, 20% for $k=3$ and 28% for $k=4$. So the global minimiser is not in general the complement of an edge, and `KServer.workFnU_duality` cannot be quoted.
--
--   A neighbouring guess, that the global minimiser can always be taken injective and $r$-avoiding, is **false**, and instructively so: at $\sigma=\varnothing$ the work function is $\widehat w(X)=\mathrm{match}(C_0,X)$, whose only minimiser of $\widehat w-D$ is $C_0$ itself, so a non-injective $C_0$ is an immediate counterexample. Exact DP over non-injective $C_0$ confirms it (56–92 failing steps per $(k,n)$ cell tested), while the restricted statement above survived all $3920$ steps of the same sweep.
--
--   **Formalization Note** Both conclusions are stated as universally quantified inequalities rather than $\arg\min$ memberships, so no minimiser is asserted to exist; on a finite metric space, which is the case of interest, one does. A proof of the general case needs either a form of quasiconvexity whose hybrids stay injective for configurations differing in more than two points, or a route that does not pass through quasiconvexity at all.
-- source:
--   E. Koutsoupias, On-line algorithms and the k-server conjecture, PhD thesis / manuscript, https://cgi.di.uoa.gr/~elias/publications/paper-kou94.pdf, Section 2.5 (the case of k+2 points), where the minimiser is required to be the complement of an edge of a spanning tree; originally E. Koutsoupias, C. Papadimitriou, The 2-evader problem, Information Processing Letters 57 (1996) 249-252, https://doi.org/10.1016/0020-0190(96)00010-5.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_duality_injective (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M)
    (hAinj : Function.Injective A) (hAr : ∀ i, A i ≠ r)
    (hA : ∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
      workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i)) :
    (∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
        workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
          ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i)) ∧
    (∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
          ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A) := by sorry

end KServer
