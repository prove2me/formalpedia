-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_5_2
-- name    : MeanBudgetXC.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:14:27.307212+00:00
-- url     : https://prove2.me/theorems/6f36ebe7-60df-4215-87de-1d0b76c762d1
-- title:
--   Theorem 5.2 — a common lifted-3XOR graph family with nonnegative rank $2^{c_R n_{\mathrm{src}}^\kappa}$
-- statement:
--   Let a 3XOR instance on $n$ base variables have $m=100n$ clauses, each with an ordered scope $I_e$ of three distinct variables and a right-hand side $b_e\in\mathbb F_2$. Let $\ell=\lceil L_{\mathrm{lift}}\log_2n\rceil$, $A=\mathbb F_2^\ell$, let $g$ be the gadget $g(x,y)=(x+e_1)\cdot(y+e_1)+1$ of (51), and for $x,y\in A^n$ let $F_y(x)$ be the number of clauses satisfied by $(g(x_i,y_i))_{i=1}^n$. For a graph $G$ write $\mathrm{Cut}_G(z)$ for the number of edges cut by a $\{0,1\}$-labelling $z$ and $\mathrm{OPT}(G)=\max_z\mathrm{Cut}_G(z)$.
--
--   There are absolute constants $D,c_\lambda,c_R>0$ and $\kappa=1/(1+3L_{\mathrm{lift}})>0$ such that, for every sufficiently large integer $n_{\mathrm{src}}$, there are such an instance, simple unit-edge graphs $G_y$ ($y\in A^n$) on one common $n_{\mathrm{src}}$-vertex set, one common cut map $x\mapsto\phi(x)\in\{0,1\}^{n_{\mathrm{src}}}$, and query-independent $\beta,\lambda,m>0$ with
--   $$\Delta(G_y)\le D,\qquad\lambda m\ge c_\lambda n_{\mathrm{src}},\qquad\mathrm{Cut}_{G_y}(\phi(x))=\beta+\lambda F_y(x),\qquad\mathrm{OPT}(G_y)\le\beta+\tfrac{31}{50}\lambda m.$$
--   The matrix $\big(\lambda(\tfrac34m-F_y(x))\big)_{y,x}$ has nonnegative rank at least $2^{c_Rn_{\mathrm{src}}^\kappa}$.
--
--   Consequently, consider a common LP with one feasible representation for each encoded cut: an output polyhedron $K$ with an $s$-inequality extended formulation and points $r_x\in K$. If its affine query objectives $z\mapsto w_y\cdot z+c_y$ reproduce the cut scores, $w_y\cdot r_x+c_y=\mathrm{Cut}_{G_y}(\phi(x))$, and each optimum is at most $\beta+\tfrac34\lambda m$, then
--   $$s\ge2^{c_Rn_{\mathrm{src}}^\kappa}-1.$$
--
--   This is the source of hardness for all approximate lower bounds of the paper: every query is a cut problem on the same vertex set with the same encoding of each row.
--
--   **Formalization Note** $L_{\mathrm{lift}}>0$ is an absolute constant and fixes $\kappa$. The instance, $n$, $\beta$, $\lambda$, the graphs and the cut map are chosen after $n_{\mathrm{src}}$. The common vertex set is `Fin n_src` and $\mathbb F_2$ is `ZMod 2`.
--
--   Differences from the source:
--   - reading: "The functions $F_y(x)$ count satisfied clauses in a lifted 3XOR instance" (p.22), with $x,y,m$ left implicit → an existential 3XOR instance on $n$ variables with $m=100n$ distinct-variable clauses, gadget length $\ell=\lceil L_{\mathrm{lift}}\log_2n\rceil$, rows and queries $x,y\in(\mathbb F_2^\ell)^n$, and $F_y(x)$ the lifted clause count with gadget (51), all chosen after $n_{\mathrm{src}}$; reason: these are the objects Appendix D attaches to the theorem (Notation and D.1, pp.42–43); the theorem asserts their existence for each large $n_{\mathrm{src}}$
--   - encoding: nonnegative rank at least $2^{c_Rn_{\mathrm{src}}^\kappa}$ → every nonnegative factorization (`HasNonnegFactorization`, platform) has inner dimension at least $2^{c_Rn_{\mathrm{src}}^\kappa}$; reason: the nonnegative rank is the least such inner dimension
--   - encoding: a common LP with one feasible representation per encoded cut, affine objectives reproducing the cut scores, each optimum at most $\beta+\frac34\lambda m$ → any $K$ with `IsEFOfSize K s` in a finite output space, points $r_x\in K$, objectives $w_y\cdot z+c_y$ with $w_y\cdot r_x+c_y=\mathrm{Cut}_{G_y}(\phi(x))$ and $w_y\cdot z+c_y\le\beta+\frac34\lambda m$ on $K$; reason: an optimum over $K$ is at most the bound iff the objective is at most the bound on all of $K$
--   - encoding: a cut map $\phi(x)\in\{0,1\}^{n_{\mathrm{src}}}$, $\mathrm{Cut}_G(z)=\sum_{ij\in E(G)}\mathbf 1[z_i\ne z_j]$, $\mathrm{OPT}(G)=\max_z\mathrm{Cut}_G(z)$ → $\phi(x)$ a vertex set (the side labelled $1$), with the published `MISInducedMinor.cutCount` (edges with exactly one end in the set) and `MISInducedMinor.maxCut` (its maximum over all sets); reason: a labelling and its set of $1$s determine each other, and an edge is cut iff exactly one end is in the set
--   - encoding: the gadget term $x_1+y_1$ → a sum over the coordinates of index $0$; reason: equal for $\ell\ge1$, which holds since an instance with three distinct variables per clause has $n\ge3$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 5.2, pp.22–23; the objects $F_y(x)$, $\ell$, $g$ and the instance are those of Appendix D, Notation and D.1, pp.42–43

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_MISInducedMinor_maxCut
import Definitions.Def_MeanBudgetXC_Supplement_liftedCount

namespace MeanBudgetXC.Supplement

open Matrix ExtensionComplexity.TSP

/-- **Theorem 5.2** (A common family of graphs at every sufficiently large size) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 5.2, pp.22–23; the objects are those of Appendix D, pp.42–43). There
are absolute constants `D, c_λ, c_R > 0` and `κ = 1/(1 + 3 L_lift) > 0` such that, for every
sufficiently large integer `n_src`, there are simple unit-edge graphs `G_y` on one common
`n_src`-vertex universe, one common cut map `ϕ(x)`, and query-independent `β, λ, m > 0` with
`Δ(G_y) ≤ D`, `λm ≥ c_λ n_src`, `Cut_{G_y}(ϕ(x)) = β + λ F_y(x)`, `OPT(G_y) ≤ β + (31/50) λ m`.
The matrix `(λ(3m/4 − F_y(x)))_{y,x}` has nonnegative rank at least `2^{c_R n_src^κ}`.
Consequently, consider a common LP with one feasible representation for each encoded cut. If its
affine query objectives reproduce these cut scores and each optimum is at most `β + (3/4) λ m`,
then the LP has at least `2^{c_R n_src^κ} − 1` inequalities.

**Formalization Note** `F_y(x)` is the lifted 3XOR clause count of Appendix D (p.43): a 3XOR
instance on `n` variables with `m = 100 n` clauses on three distinct variables, the gadget (51) of
length `ℓ = ⌈L_lift log₂ n⌉` over `A = F₂^ℓ`, and rows and queries `x, y ∈ A^n`
(`liftedCount I y x`). `L_lift > 0` is absolute and fixes `κ`; `n`, the instance, `β`, `λ`, the
graphs `G_y` on `Fin n_src` (one per query `y`) and the one cut map `ϕ` are chosen after `n_src`.
A cut is given by the side `A = ϕ(x) ⊆ V` of the label `1`; `Cut_G` and `OPT(G)` are the
published `MISInducedMinor.cutCount` (edges with exactly one end in `A`) and
`MISInducedMinor.maxCut` (its maximum over all `A`). The nonnegative-rank bound is stated
against every nonnegative factorization (the platform's
`HasNonnegFactorization`). In the LP consequence, the LP's output polyhedron is any `K` with an
`s`-inequality formulation `IsEFOfSize K s` in any finite output space, `pt x ∈ K` is the
representation of the encoded cut `ϕ(x)`, and query `y` has the affine objective
`z ↦ w_y · z + c_y`. -/
theorem theorem_5_2 :
    ∃ D cLam cR : ℝ, 0 < D ∧ 0 < cLam ∧ 0 < cR ∧ ∃ Llift : ℝ, 0 < Llift ∧ ∃ N₀ : ℕ, ∀ nsrc ≥ N₀,
      ∃ (n ℓ : ℕ) (I : XOR3Instance n (100 * n)), ℓ = ⌈Llift * Real.logb 2 n⌉₊ ∧
      ∃ β lam : ℝ, 0 < β ∧ 0 < lam ∧ 0 < 100 * n ∧
      ∃ (G : (Fin n → Fin ℓ → ZMod 2) → SimpleGraph (Fin nsrc)) (_ : ∀ y, DecidableRel (G y).Adj)
        (φ : (Fin n → Fin ℓ → ZMod 2) → Finset (Fin nsrc)),
        (∀ y, ((G y).maxDegree : ℝ) ≤ D) ∧
        cLam * nsrc ≤ lam * ((100 * n : ℕ) : ℝ) ∧
        (∀ x y, (MISInducedMinor.cutCount (G y) (φ x) : ℝ) = β + lam * liftedCount I y x) ∧
        (∀ y, (MISInducedMinor.maxCut (G y) : ℝ) ≤ β + 31 / 50 * lam * ((100 * n : ℕ) : ℝ)) ∧
        (∀ r : ℕ, HasNonnegFactorization
            (fun y x : Fin n → Fin ℓ → ZMod 2 =>
              lam * (3 / 4 * ((100 * n : ℕ) : ℝ) - liftedCount I y x)) r →
          (2 : ℝ) ^ (cR * (nsrc : ℝ) ^ (1 / (1 + 3 * Llift))) ≤ r) ∧
        ∀ (ι : Type) [Fintype ι] (K : Set (ι → ℝ)) (s : ℕ), IsEFOfSize K s →
          ∀ (pt : (Fin n → Fin ℓ → ZMod 2) → ι → ℝ) (w : (Fin n → Fin ℓ → ZMod 2) → ι → ℝ)
            (c₀ : (Fin n → Fin ℓ → ZMod 2) → ℝ),
            (∀ x, pt x ∈ K) →
            (∀ x y, w y ⬝ᵥ pt x + c₀ y = MISInducedMinor.cutCount (G y) (φ x)) →
            (∀ y, ∀ z ∈ K, w y ⬝ᵥ z + c₀ y ≤ β + 3 / 4 * lam * ((100 * n : ℕ) : ℝ)) →
            (2 : ℝ) ^ (cR * (nsrc : ℝ) ^ (1 / (1 + 3 * Llift))) - 1 ≤ s := by sorry

end MeanBudgetXC.Supplement
