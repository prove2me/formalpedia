-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleGeometryPrescribedScale_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:06:35.316925+00:00
-- url     : https://prove2.me/theorems/3e87765a-a762-4238-9442-8869eabbcd35
-- title:
--   The prepared finite-schedule geometry statement at a prescribed scale holds under counting hypotheses
-- statement:
--   Let $m$ be a natural number, $K$ a finite type (in universe $0$) indexing a finite schedule, and $\mathrm{degree}, C_{\mathrm{detect}} : K \to \mathbb{N}$. Let $G$ be a finite type with decidable equality, $I_j$ finite types for $j < m$, $n_j$ natural numbers, and $B(a)$, for each layer-sampler axis $a$ (an element of `LayerSamplerAxis I n`), a finite type with decidable equality (all types in universe $0$). Let $B_{\mathrm{struct}}, p_{\mathrm{num}}, Q_{\mathrm{stride}}$ be reals, $n_X$ a natural number, and $p_{\mathrm{detect}}, a_{\mathrm{detect}}, \mathrm{target} : K \to \mathbb{R}$. Assume:
--   - $m > 0$, and $\mathrm{degree}(s) \le m$ for every $s \in K$;
--   - $0 \le B_{\mathrm{struct}}$ and $0 \le p_{\mathrm{num}} \le B_{\mathrm{struct}}$;
--   - the number of variables $\lvert\texttt{LayerSamplerVariables G I n B}\rvert$ is at most $p_{\mathrm{num}}$, and $\lvert I_j\rvert \le p_{\mathrm{num}}$ and $n_j \le p_{\mathrm{num}}$ for every $j$;
--   - for every $s \in K$ and every axis $b = (j, \ldots)$, the number of elements of `boundedBooleanJetRows (Fin (degree s + 1)) (j + 1)` is at most $\lvert B(b)\rvert$;
--   - $p_{\mathrm{detect}}(s) \ge 0$, $a_{\mathrm{detect}}(s) \ge 0$ and $\mathrm{target}(s) \ge 0$ for every $s$, and $Q_{\mathrm{stride}} \ge 0$.
--
--   Then `PreparedFiniteScheduleGeometryPrescribedScaleStatement m degree Cdetect B nX pDetect aDetect target` holds (with the given $G$, $B_{\mathrm{struct}}$, $p_{\mathrm{num}}$, $Q_{\mathrm{stride}}$). This proposition is defined by OpenAI. In outline it says: with a radius constant $A_{\mathrm{radius}}$ chosen from OpenAI's theorem `exists_preparedUniformEarlyRadius m`, the radius logarithm `allocatedCommonProductRadiusLog m Bstruct Bstruct` lies in $[0, (2B_{\mathrm{struct}} + A_{\mathrm{radius}})^{A_{\mathrm{radius}}}]$, the common radius $R$ = `allocatedCommonProductRadius m Bstruct Bstruct` satisfies $0 < R \le 1$ and $R^{-1} \le e^{\text{radius log}}$, the explicit dimension, gain, kernel, profile and tail budgets are nonnegative, and there are tolerances $t(s) \in (0, 1]$ with $t(s)^{-1}$ bounded by the tail budget such that for every $Q_\sigma \ge 0$ the uniform tolerance $\sigma$ = `preparedUniformDegreeTolerance t Qσ` and scale `preparedUniformDegreeScaleLog` satisfy explicit bounds, and for all subspaces $U_j$, bases of their orthogonal complements and every `LayerSamplerScale` $S$ with radii $R$ and tolerance $\sigma$ whose side `S.value` is at least $\exp$ of every length budget `allocatedAffineLengthLog …`, the geometry `PreparedUniformDegreeGeometryAt` holds at every schedule point $s \in K$. The precise content is OpenAI's Lean definition.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B272` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B272

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleGeometryPrescribedScale_s2 (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
    (hm : 0 < m) (hdegree : ∀ s, degree s ≤ m) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ s : K, ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin ((degree s) + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : ∀ s, 0 ≤ pDetect s) (ha : ∀ s, 0 ≤ aDetect s) (hQstride : 0 ≤ Qstride)
    (htarget : ∀ s, 0 ≤ target s) :
    PreparedFiniteScheduleGeometryPrescribedScaleStatement (G := G) m degree Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (Qstride := Qstride) nX pDetect aDetect target := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
