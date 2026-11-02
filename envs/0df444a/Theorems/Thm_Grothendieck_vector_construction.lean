-- Prove2me | Theorems.Thm_Grothendieck_vector_construction
-- name    : Grothendieck.vector_construction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:18:38.692455+00:00
-- url     : https://prove2.me/theorems/8fa286a5-7677-4e2c-881c-cfe5d004004f
-- title:
--   Lemma 4.1 — constructing the vectors that linearize the rounding expectation
-- statement:
--   Let $G=(V,E)$ be a graph with at least one edge, let $r\ge1$, and let $f:V\to S^{|V|-1}$ be a function into the unit sphere of $\mathbb R^{|V|}$. Then there is a function $g:V\to S^{|V|-1}$ such that for every edge $\{u,v\}$ of $G$
--
--   $$
--   E_r\big(g(u)\cdot g(v)\big)=\beta(r,G)\,\big(f(u)\cdot f(v)\big),
--   $$
--
--   where $\beta(r,G)$ is the solution of $\sum_{k\ge0}|b_{2k+1}|\beta(r,G)^{2k+1}=1/(\vartheta(G)-1)$.
--
--   This is the lemma that makes the rounding argument linear. Applying the Gaussian rounding directly to an optimal solution $f$ would produce an expectation $\mathbb E[h(u)\cdot h(v)]=E_r(f(u)\cdot f(v))$, which is a nonlinear function of $f(u)\cdot f(v)$ and cannot be compared with $\sum_{\{u,v\}\in E}A(u,v)f(u)\cdot f(v)$; the construction replaces $f$ by $g$ so that the expectation becomes exactly proportional to the original inner product, edge by edge.
--
--   The proof has three steps. First, in the Hilbert space $\mathcal H=\bigoplus_{k\ge0}(\mathbb R^{|V|})^{\otimes(2k+1)}$, the vectors $S(x)$ and $T(x)$ with components $\sqrt{|b_{2k+1}|}\beta^{2k+1}x^{\otimes(2k+1)}$ and $\operatorname{sign}(b_{2k+1})$ times those satisfy $S(x)\cdot T(y)=E_r^{-1}(\beta\,x\cdot y)$ and $S(x)\cdot S(x)=T(x)\cdot T(x)=1/(\vartheta(G)-1)$, which is exactly where the series with absolute values enters. Second, an optimal solution $Z$ of the theta program is turned into two vector families $s,t$ with $s(u)\cdot s(v)=t(u)\cdot t(v)=0$ and $s(u)\cdot t(v)=1/2$ across edges, and constant norm $(\vartheta(G)-1)/2$, through the two-block matrix $U=\left(\begin{smallmatrix}A&B\\B&A\end{smallmatrix}\right)$. Third, $R(u)=s(u)\otimes S(f(u))+t(u)\otimes T(f(u))$ has $R(u)\cdot R(v)=E_r^{-1}(\beta\,f(u)\cdot f(v))$ and unit norm, and the Gram matrix of the $R(u)$ yields $g$ by Cholesky decomposition.
--
--   **Formalization Note** The spheres are `EuclideanSpace ℝ V`, i.e. $\mathbb R^{|V|}$ with the vertex set as index; the conclusion is stated for edges, i.e. under the hypothesis `G.Adj u v`.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Lemma 4.1, p. 92, and its proof, pp. 94-95. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Beta

namespace Grothendieck

theorem vector_construction {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v)
    (f : V → EuclideanSpace ℝ V) (hf : ∀ v, ‖f v‖ = 1) :
    ∃ g : V → EuclideanSpace ℝ V, (∀ v, ‖g v‖ = 1) ∧
      ∀ u v, G.Adj u v → Er r (inner ℝ (g u) (g v)) = beta r G * inner ℝ (f u) (f v) := by sorry

end Grothendieck
