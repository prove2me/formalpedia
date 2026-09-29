-- Prove2me | Theorems.Thm_KServer_mst_cut_property
-- name    : KServer.mst_cut_property
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T10:43:26.294838+00:00
-- url     : https://prove2.me/theorems/39e9826c-c9e6-4931-bdc4-7d1b2436e2fc
-- title:
--   The cut property of minimum spanning trees
-- statement:
--   A **rooted spanning structure** on a finite type $V$ is a triple: a root $\rho$, a parent map $\mathrm{par}:V\to V$ and a rank certificate $\mathrm{rk}:V\to\mathbb N$ with $\mathrm{rk}(\rho)=0$, with $\rho$ the only vertex of rank $0$, and with $\mathrm{rk}(\mathrm{par}(v))<\mathrm{rk}(v)$ for every $v\neq\rho$. Following parents strictly decreases the rank, so every vertex reaches the root; the edges $\{v,\mathrm{par}(v)\}$ for $v\neq\rho$ therefore form a spanning tree of $V$, and conversely every spanning tree arises this way (take $\mathrm{rk}$ to be the depth from any chosen root). Its weight for a symmetric $\omega$ is
--   $$\mathrm{wt}(\rho,\mathrm{par})=\sum_{v\neq\rho}\omega\bigl(v,\mathrm{par}(v)\bigr).$$
--
--   **Statement.** If $\omega(r,a)$ is a minimum-weight edge at $r$ — that is, $\omega(r,a)\le\omega(r,b)$ for every $b\neq r$ — then every rooted spanning structure can be replaced by one of no larger weight that is rooted at $a$ and has $\mathrm{par}(r)=a$, so that its tree contains the edge $\{r,a\}$.
--
--   This is the **cut property** of minimum spanning trees, for the cut $(\{r\},V\setminus\{r\})$: some minimum spanning tree contains a minimum-weight edge crossing it. Taking the minimum of the conclusion over all structures gives
--   $$\min_{T}\ \mathrm{wt}(T)\ =\ \min_{T\ni\{r,a\}}\ \mathrm{wt}(T),$$
--   which is the form in which the cut property is normally used.
--
--   **Role.** It is the combinatorial half of the Koutsoupias–Papadimitriou argument for metric spaces with exactly $k+2$ points. There the potential is a minimum over spanning trees $T$ of the $k+2$ points,
--   $$\Psi(w;T)=\sum_{X\in T}w(X^C)-\sum_{[a,b]\notin T}d(a,b),\qquad \Psi(w;T)+C(V)=\sum_{X\in T}\bigl[w(X^C)+d(X)\bigr],$$
--   so up to the constant $C(V)$ the potential is the weight of a minimum spanning tree for $\omega(u,v)=w(\{u,v\}^C)+d(u,v)$; a spanning tree of $k+2$ points has $k+1$ edges, hence $k+1$ work-function values, hence the competitive ratio $k$. The scheme needs the minimum to be attained at a tree containing the edge whose complement is a minimiser of the request, and that edge is exactly a minimum-weight edge at $r$. Mathlib has no minimum-spanning-tree theory, so the lemma has to be built.
--
--   **Formalization Note** The statement is deliberately free of any graph-theoretic definition: a spanning tree is presented as a parent map with a rank certificate, which makes acyclicity automatic and needs no `SimpleGraph`. Both hypotheses and conclusion are in the same form, so the lemma composes with itself. A proof can go by re-rooting followed by a single exchange: re-rooting at $a$ preserves the edge multiset and hence the weight, and once $a$ is the root, redefining $\mathrm{par}(r):=a$ is automatically legal because $\mathrm{rk}(a)=0$ is below every other rank — this removes the edge $\{r,\mathrm{par}(r)\}$, which is incident to $r$, and inserts $\{r,a\}$, so the minimality hypothesis gives the inequality. Re-rooting itself follows by induction on $\mathrm{rk}(a)$ from the one-step case where $a$ is a child of the root, for which the new parent map is $\mathrm{par}[\rho\mapsto a]$ and the new rank is $0$ at $a$, $1$ at $\rho$ and $\mathrm{rk}+1$ elsewhere.
-- source:
--   T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, Introduction to Algorithms, Chapter on minimum spanning trees (Theorem: a light edge crossing a cut is safe); used in this form in E. Koutsoupias, On-line algorithms and the k-server conjecture, https://cgi.di.uoa.gr/~elias/publications/paper-kou94.pdf, Section 2.5, which cites [32, Chapter 12] for 'for each node a and a minimum weight edge X adjacent from a, there is a minimum spanning tree that contains X'.

import Mathlib

namespace KServer

theorem mst_cut_property {V : Type} [Fintype V] [DecidableEq V] (ω : V → V → ℝ)
    (hsymm : ∀ u v, ω u v = ω v u) (r a : V) (hra : r ≠ a)
    (hmin : ∀ b, b ≠ r → ω r a ≤ ω r b)
    (ρ : V) (par : V → V) (rk : V → ℕ)
    (hrk : rk ρ = 0) (huniq : ∀ v, rk v = 0 → v = ρ)
    (hpar : ∀ v, v ≠ ρ → rk (par v) < rk v) :
    ∃ (par' : V → V) (rk' : V → ℕ),
      rk' a = 0 ∧ (∀ v, rk' v = 0 → v = a) ∧ (∀ v, v ≠ a → rk' (par' v) < rk' v) ∧
      par' r = a ∧
      (∑ v ∈ Finset.univ.erase a, ω v (par' v))
        ≤ ∑ v ∈ Finset.univ.erase ρ, ω v (par v) := by sorry

end KServer
