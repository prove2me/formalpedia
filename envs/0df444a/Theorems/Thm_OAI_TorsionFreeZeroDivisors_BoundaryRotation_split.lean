-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_BoundaryRotation_split
-- name    : OAI.TorsionFreeZeroDivisors.BoundaryRotation.split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:11:54.931771+00:00
-- url     : https://prove2.me/theorems/1e92ab11-0319-4634-9fa9-c70d135ef903
-- title:
--   Lemma 4.4 (OpenAI), separator step — a genus-zero boundary pairing has a Lipton–Tarjan split
-- statement:
--   Let $T$ be a finite set of boundaries with lengths $\ell(t)>0$, and let the positions be the pairs $(t,q)$ with $0\le q<\ell(t)$. Let $\sigma$ be the rotation $(t,q)\mapsto(t,q+1\bmod\ell(t))$, and let $\alpha$ be an involution of the positions. Assume the genus-zero equation
--
--   $$2\,c(\sigma)+2\,c(\alpha\sigma)=|\operatorname{supp}\alpha|+4\,k(\sigma,\alpha),$$
--
--   where $c$ counts cycles (fixed points included), $\alpha\sigma$ is $x\mapsto\alpha(\sigma(x))$, and $k$ counts the orbits of $\langle\sigma,\alpha\rangle$. Write $p\sim r$ when some position of boundary $p$ is paired by $\alpha$ with a position of boundary $r$. Then every finite $S\subseteq T$ has a split: a set $X\subseteq S$ and a family $\mathcal B$ of pairwise disjoint sets with $\bigcup\mathcal B=S\setminus X$, such that
--
--   1. each $B\in\mathcal B$ is closed under $\sim$ within $S\setminus X$: if $x\in B$, $y\in S\setminus X$ and $x\sim y$, then $y\in B$;
--   2. $3|B|\le2|S|$ for each $B\in\mathcal B$;
--   3. $|X|\le2\sqrt2\,\sqrt{|S|}$.
--
--   This is the planar separator theorem of Lipton and Tarjan for the graph that a planar pairing of boundary positions induces on the boundaries. Removing at most $2\sqrt{2|S|}$ boundaries leaves pieces of at most two thirds of the size.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 17: “Lemma 4.4 (Recursive planar separation). Put $C_{\mathrm{sep}} = \frac{2\sqrt2}{1-\sqrt{2/3}}$. For every integer $K \ge 1$, a planar multigraph with $m$ vertices has a set of at most $C_{\mathrm{sep}} m/\sqrt K$ vertices whose deletion leaves components of size at most $K$.” Its proof applies “The planar separator theorem of Lipton and Tarjan [14, Corollary 2, p. 183] … in any simple planar graph with $s$ vertices, at most $2\sqrt{2s}$ vertices whose deletion leaves components with at most $2s/3$ vertices” recursively. This statement is that one step, for the planar multigraphs that arise in Proposition 4.5 (R. J. Lipton and R. E. Tarjan, A separator theorem for planar graphs, SIAM J. Appl. Math. 36 (1979) 177–189, [doi:10.1137/0136016](https://doi.org/10.1137/0136016)). The recursion is carried out inside the proofs of `OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded` and `OAI.TorsionFreeZeroDivisors.ConcreteFactors.both_nonzero`.
--
--   **Formalization note.** Positions are `ComparedBlocks.Position len`, $\sigma$ is `BoundaryRotation.perm len`, the genus-zero equation is `MapEuler.GenusZero`, $\sim$ is `PairingClusters.Rel`, and a split is a `RecursiveSeparator.Split`, all from the bundle `Def_TorsionFreeZeroDivisorsConstruction`. $\mathcal B$ may contain empty sets. Relations with boundaries outside $S\setminus X$ impose nothing.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 17, Lemma 4.4 (recursive planar separation), one step: the planar separator theorem of Lipton and Tarjan (SIAM J. Appl. Math. 36 (1979) 177-189, https://doi.org/10.1137/0136016, Corollary 2, p. 183) for the pairing graph of a genus-zero boundary pairing; Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), BoundaryRotation.split

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.BoundaryRotation

open scoped Classical
open ComparedBlocks

theorem split {T : Type} [Fintype T] (len : T→ℕ) (hpos : ∀t,0<len t)
    (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) (S : Finset T) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel (fun x : Position len => x.1) α) S) := by
  sorry

end OAI.TorsionFreeZeroDivisors.BoundaryRotation
