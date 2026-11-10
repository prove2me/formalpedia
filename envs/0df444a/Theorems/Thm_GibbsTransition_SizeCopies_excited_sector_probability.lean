-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_excited_sector_probability
-- name    : GibbsTransition.SizeCopies.excited_sector_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:52:41.477208+00:00
-- url     : https://prove2.me/theorems/4a193d3c-49a9-4ab3-a9f1-950d7ef348bf
-- title:
--   Lemma 5.2 — Probability of the excited sector
-- statement:
--   Let $0<\varepsilon\le1/16$ be rational, choose rational $\varepsilon'\in(\varepsilon/2,\varepsilon]$, and let $\beta>0$ be rational. Put $R=\lfloor\kappa/\varepsilon\rfloor$ and take the two ferromagnets $r_0=0$ and $r_1=4\varepsilon'$. For either instance, every real field $\phi\in[0,1]$, and every integer $1\le L\le R$, the probability that the Gibbs configuration contains $C$ is at most
--
--   $$\xi_{\beta,R}=\frac{(12R^3)^6}{6!}e^{-2\kappa\beta}\exp\!\left(R^3e^{-\kappa\beta}+12R^3e^{-\kappa\beta/3}\right).$$
--
--   Moreover,
--
--   $$\kappa\beta\ge48\log(12(R+1))\quad\Longrightarrow\quad\xi_{\beta,R}\le(R+1)^{-3}.$$
--
--   The probability is computed from the actual Gibbs density's diagonal, uniformly over both physical instances, all admissible sizes and all fields. It controls the thermal sector that distinguishes the transition targets.
--
--   Differences from the source:
--   - encoding: either of the two ferromagnetic instances and its C-sector probability → Fin 2 indexes the actual pair and the Born probability sums the C-containing diagonal entries; reason: the pair and event are constructed from the source matrices, rather than supplied as arbitrary probability laws
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §5.2 preamble and Lemma 5.2, Equation (30), printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Physics

namespace GibbsTransition.SizeCopies

/-- Lemma 5.2, with all of the §5.2 preamble. No field/size is fixed
by the model and neither hard instance is supplied as a hypothesis. -/
theorem excited_sector_probability (epsilon epsilon' beta : ℚ)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1/16)
    (hep0 : epsilon/2 < epsilon') (hep1 : epsilon' ≤ epsilon)
    (hb : 0 < beta) :
    let R := ⌊kappa / (epsilon : ℝ)⌋₊
    (∀ (i : Fin 2) (L : ℕ), 1 ≤ L → L ≤ R →
      ∀ phi ∈ Set.Icc (0 : ℝ) 1,
        excitedProbability (if i = 0 then 0 else 4*(epsilon' : ℝ)) L phi beta ≤
          xi beta R) ∧
    (48 * Real.log (12 * ((R : ℝ)+1)) ≤ kappa*(beta : ℝ) →
      xi beta R ≤ (((R : ℝ)+1)^3)⁻¹) := by sorry

end GibbsTransition.SizeCopies
