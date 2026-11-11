-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_34
-- name    : GaussLocalMaxColoring.Main.lemma_34
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:24:45.900862+00:00
-- url     : https://prove2.me/theorems/94e3f670-a9cc-461d-917a-d59215581811
-- title:
--   Lemma 34 — BuildVector: certified vectors and band witnesses in polynomial time
-- statement:
--   There is a deterministic polynomial-time program BuildVector that, given a 3-colorable graph $G$ on $n\ge2$ vertices and a band partition $\mathcal P$ of $[-\tfrac12,1]$ (rational endpoints), returns the Gram matrix $X$ of unit vectors $\{v_i\}$ with
--   $$-\tfrac12\le\langle v_i,v_j\rangle\le1,\quad \langle v_i,v_j\rangle\le-\tfrac12+\varepsilon_{\rm SDP}\ (ij\in E),\quad \langle v_i,v_j\rangle+\langle v_i,v_{j'}\rangle\le\tfrac12\ (jj'\in E,\ i\notin\{j,j'\}),\quad \Gamma_{rx}(X)\succeq-\varepsilon_{\rm SDP}I\ (rx\in E),$$
--   and for every $r\in V$, $P\in\mathcal P$, $S=S_{r,P}$, the Gram matrix of a witness $\mathcal W_{r,P}$ that is (i) for positive $P$ feasible for $\Theta_1(S)$ with $\sum_{j\in S}\|x_j\|^2\ge\sum_{j\in S}\frac{1+2\langle v_r,v_j\rangle}3-\varepsilon_{\rm SDP}\ge\frac{1+2\rho_P}3|S|-\varepsilon_{\rm SDP}$, (ii) for negative $P$ feasible for $\Theta_2(S)$ with $\sum_{j\in S}(\|x_{j,1}\|^2+\|x_{j,2}\|^2)\ge\sum_{j\in S}\frac{2-2\langle v_r,v_j\rangle}3-\varepsilon_{\rm SDP}\ge\frac{2-2\rho_P}3|S|-\varepsilon_{\rm SDP}$; $\varepsilon_{\rm SDP}=e^{-3n}$. The running time is polynomial in $n+|\mathcal P|$ (polynomial in $n$ and $\log(1/\varepsilon_{\rm SDP})=3n$ for $|\mathcal P|=O(\log n)$).
--
--   Differences from the source:
--   - encoding: a subroutine returning ({v_i}, 𝒮) with real vectors and witness vectors, running in time polynomial in n and log(1/ε_SDP) → a deterministic CongruencyTU program (DetSolves, input size n + |𝒫|) returning rational positive semidefinite Gram matrices of {v_i} and of each witness 𝒲_{r,P}, all guarantees stated on these matrices; reason: the vectors are a Gram realization of X (Algorithm 6, line 3) and every listed property depends only on Gram matrices; a bit-model machine returns rationals
--   - generalization: one partition 𝒫 fixed by the algorithm (§5.2) → the partition is an input: every band partition with rational endpoints, time polynomial in n + |𝒫|; reason: the paper's fixed partition can be taken with rational endpoints and O(log n) intervals, where the bound is polynomial in n
--   - encoding: graph G = (V, E) as input → Graph3 on Fin n via the published adjacency-matrix encoding encGraph, followed by the partition; reason: machine input layout
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 34, printed p. 33 (PDF 35); Appendix B.1 (pp. 67–70, PDF 69–72)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_GaussLocalMaxColoring_Main_Machine

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 34** (Certified vectors and band witnesses; p. 33, PDF 35). There is a deterministic
polynomial-time subroutine BuildVector (a program of the integer RAM `CongruencyTU`) that, given a
3-colorable graph `G` on `n ≥ 2` vertices (and the band partition `𝒫`), returns the Gram matrix
`X` of unit vectors `{v_i}` with `−1/2 ≤ ⟨v_i, v_j⟩ ≤ 1`, `⟨v_i, v_j⟩ ≤ −1/2 + ε_SDP` on edges,
`⟨v_i, v_j⟩ + ⟨v_i, v_j′⟩ ≤ 1/2` for `jj′ ∈ E`, `i ∉ {j, j′}`, `Γ_rx(X) ⪰ −ε_SDP I` for `rx ∈ E`, and
for every `r ∈ V`, `P ∈ 𝒫` the Gram matrix of a band witness feasible for `Θ₁(S_{r,P})` (`P`
positive) or `Θ₂(S_{r,P})` (`P` negative) with the mass bounds (i), (ii); `ε_SDP = e^{−3n}`. -/
theorem lemma_34 : CongruencyTU.DetSolves encBV sizeBV DomBV GoodBV := by sorry

end GaussLocalMaxColoring.Main
