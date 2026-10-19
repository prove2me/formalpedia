-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedUniformDegreeComparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:58:02.717326+00:00
-- url     : https://prove2.me/theorems/069ff500-1b59-4c44-9cc7-7cab7ee20c64
-- title:
--   Existence of a prepared uniform-degree comparison with explicit profile and tail budgets
-- statement:
--   Let $m, s$ be natural numbers; let $G$ be a finite type with decidable equality; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types (in `Type`), $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types with decidable equality indexed by the sampler axes $a$ in `LayerSamplerAxis I n`. Write $K$ = `LayerSamplerVariables G I n B` (a finite type defined by OpenAI). Let $p_{\mathrm{num}}, p_{\mathrm{Detect}}, a_{\mathrm{Detect}}, \mathrm{target}, Q_{\mathrm{stride}}$ be reals, and assume:
--   - $0 < m$ and $s \le m$;
--   - $0 \le p_{\mathrm{num}}$, $|K| \le p_{\mathrm{num}}$, and $|I_j| \le p_{\mathrm{num}}$ and $n_j \le p_{\mathrm{num}}$ for every $j$;
--   - for every sampler axis $b$ (with layer index $b.1 \in \mathrm{Fin}\,m$), the number of elements of `boundedBooleanJetRows (Fin (s+1)) (b.1 + 1)` (a finite set of subsets of $\mathrm{Fin}(s+1)$, defined by OpenAI) is at most $|B_b|$;
--   - $0 \le p_{\mathrm{Detect}}$, $0 \le a_{\mathrm{Detect}}$, $0 \le \mathrm{target}$, $0 \le Q_{\mathrm{stride}}$.
--
--   Let $C_{\mathrm{detect}}, n_X$ be natural numbers. Define (all functions explicit and defined by OpenAI):
--   - $D$ = `allocatedComparisonDimension m pnum`;
--   - $\mathrm{gainLog}$ = `slicedDetectionGainLog s Cdetect |K| pDetect pDetect aDetect`;
--   - $P_k$ = `scalarKernelLogarithmicBudget (Fin (s+1)) G (gainLog + pDetect + 4)`;
--   - $E = \mathrm{target} + D \cdot (m\, 2^{m+1}) \cdot P_k + 5$;
--   - $P_\rho = 2 \cdot \texttt{affineProfileInputEnvelope}\ D\ \ell_c\ \ell_t\ E\ (p_{\mathrm{Detect}} + 2) + 2$;
--   - $P_{\mathrm{tail}}$ = `affineProfileToleranceEnvelope m D (D(D+1) + D·D + D + 1)` $\ell_c\ \ell_t\ E\ (p_{\mathrm{Detect}} + 2)$,
--
--   where $\ell_c$ = `canonicalSublevelCutoffLip` and $\ell_t$ = `canonicalTransitionLip` are fixed Lipschitz constants chosen by OpenAI. Then $0 \le P_\rho$, $0 \le P_{\mathrm{tail}}$, and the type `PreparedUniformDegreeComparison B s D target P_k P_ρ P_tail pDetect` is nonempty. This is a structure defined by OpenAI recording, among other data, a choice of scale $\rho(\text{partition}) \in (0, 1]$ with $\rho^{-1} \le e^{P_\rho}$ for each partition of the sampler axes, and a parameter $t \in (0, 1]$ with $t^{-1} \le e^{P_{\mathrm{tail}}}$, together with the comparison estimates for the uniform-degree model.
--
--   (The quantities $Q_{\mathrm{stride}}$ and $n_X$, and the hypothesis $0 \le Q_{\mathrm{stride}}$, do not appear in the conclusion.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeDirectMasterBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B261` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedUniformDegreeDirectMasterBudget.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B261

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeComparison_s2
    {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {pnum pDetect aDetect target Qstride : ℝ} (hm : 0 < m) (hs : s ≤ m)
    (hnum : 0 ≤ pnum)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (htarget : 0 ≤ target) (hQ : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let D := allocatedComparisonDimension m pnum
    let gainLog := slicedDetectionGainLog s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
      (canonicalTransitionLip : ℝ) E (pDetect + 2) + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E (pDetect + 2)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B s D target Pk Prho Ptail pDetect) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
