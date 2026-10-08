-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_SpherePicture_excluded
-- name    : OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:12:00.673571+00:00
-- url     : https://prove2.me/theorems/c9ae2107-06e5-4fa7-9c81-47081b4f6ae2
-- title:
--   Proposition 4.5 (OpenAI) — without bounded systems, the sampled graph admits no reduced spherical arrangement
-- statement:
--   Let $r=(r_A,r_B)$ be a pair of matchings at level $n$ such that
--
--   1. $L=L(\mathrm{size}(n))\ge2$;
--   2. every connected component of both vertex graphs has diameter at most $D_0L$;
--   3. $r\in\mathcal S(n)$: both graphs have girth at least $L$;
--   4. for some roots $x$, $y$, the sampled graph $\Gamma=\Gamma_A\sqcup\Gamma_B$ carries no bounded system with OpenAI's fixed parameters $(C,K,I)$ of Section 4.
--
--   Then $\Gamma$ admits no reduced spherical picture with a nonempty index set $O$. Such a picture is a rotation $\sigma$ of $O$, a fixed-point-free involution $\alpha$ of $O$ pairing positions with inverse letters, and darts $\delta:O\to D$ forming closed paths along the cycles of $\sigma$, subject to the genus-zero equation $2c(\sigma)+2c(\alpha\sigma)=|O|+4k(\sigma,\alpha)$. It is reduced when $\delta(\alpha(i))\ne\overline{\delta(i)}$ and $\delta(\sigma(i))\ne\overline{\delta(i)}$ for all $i$:
--
--   $$\text{(1)–(4)}\ \wedge\ a\ \text{reduced spherical picture over } \Gamma\ \Longrightarrow\ \mathrm{False}.$$
--
--   Together with the good samples of `OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding`, this rules out reduced spherical arrangements on the chosen graphs. Through `OAI.TorsionFreeZeroDivisors.ConeTorsion.graph_torsion_free` it gives torsion-freeness of $G$.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 18: “Proposition 4.5 (Absence of reduced spherical arrangements). With probability $1 - o(1)$, $\Gamma$ admits no reduced spherical arrangement. In particular, for all sufficiently large admissible $n$ there exist graphs of the prescribed types, with girth at least $L$ and the diameter bound of Lemma 2.3, admitting no such arrangement.”
--
--   The paper's proof shows deterministically that on the diameter event, a reduced spherical arrangement contains one of the bounded systems excluded by Proposition 3.1. This statement records that deterministic step for arrangements without an exceptional rooted boundary. Rooted arrangements are handled in `OAI.TorsionFreeZeroDivisors.ConcreteFactors.both_nonzero`.
--
--   **Formalization note.** The objects are OpenAI's (`SphericalPicture.Data` and `Reduced`, `SampleGraph.BoundedSystem`, `GraphSample.Diameters`, `ActualPatternEvent.samples`, and the constants `PlanarParameters.C/K/sides` with `PathSystem.ε` and `ClosedWords.D`, from the bundle `Def_TorsionFreeZeroDivisorsConstruction`). The constants follow (4.3) of the paper, with OpenAI's choices $\varepsilon=1/2467200$, closure constant $D_0+1608$, and comparison bound $I=384\,C$. Girth is stated in the subdivision graph as $\ge3L$. The roots $x,y$ appear only in hypothesis 4, so one pair of roots without bounded systems suffices.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 18, Proposition 4.5 (absence of reduced spherical arrangements), deterministic form; Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), SampleGraph.SpherePicture.excluded

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture

open scoped Classical

theorem excluded {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
    {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)
    [Nonempty O] (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    False := by
  sorry

end OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture
