-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:26:29.019325+00:00
-- url     : https://prove2.me/theorems/6f14be0a-3aa3-4d04-8f75-e4bbc520e208
-- title:
--   The prepared finite nested source requirement is bounded by a power of p+2
-- statement:
--   Let $s, \mathrm{outerDepth}, \mathrm{innerDepth}, \mathrm{cutoff}, e, C_{\mathrm{primitive}}, C_{\mathrm{direct}}, \mathrm{extra}, \mathrm{earlybasePower}, \mathrm{inputPower} \in \mathbb{N}$ and $\mathrm{constants} : \mathbb{N} \to \mathbb{N}$, with $\mathrm{cutoff} \le \mathrm{innerDepth}$ and $1 \le \mathrm{earlybasePower}$. Then there is $\mathrm{requiredPower} \in \mathbb{N}$ with $2 \le \mathrm{requiredPower}$ such that the following holds for every real $p \ge 2$, every $m \le s$, every finite type $G$, all $M, \mathrm{count}, n_X \in \mathbb{N}$ and all reals $p_{\mathrm{num}}, Q_{\mathrm{stride}}, \mathrm{gainLog}, \mathrm{stageLog}, V_{\log}, Q_\sigma, P_{\min}, \mathrm{requestedCoarse}, \mathrm{endpoint}$. Put $q = \max(m, \mathrm{cutoff})$, $A = $ `preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra` (a natural number assembled from OpenAI's exponent functions) and $B_{\mathrm{struct}} = (p+2)^{\mathrm{earlybasePower}}$. If $p_{\mathrm{num}}, Q_{\mathrm{stride}}, \mathrm{gainLog}, \mathrm{stageLog} \in [0, B_{\mathrm{struct}}]$, $M, \mathrm{count}, n_X, |G| \le B_{\mathrm{struct}}$, and $V_{\log}, Q_\sigma, P_{\min}, \mathrm{requestedCoarse}, \mathrm{endpoint} \in [0, (B_{\mathrm{struct}} + 2)^{\mathrm{inputPower}}]$, then
--   $$\mathtt{preparedFiniteNestedSourceRequiredLog}\ q\ \mathrm{cutoff}\ A\ C_{\mathrm{direct}}\ \mathrm{outerDepth}\ \mathrm{innerDepth}\ \mathrm{constants}\ G\ M\ \mathrm{count}\ n_X\ B_{\mathrm{struct}}\ p_{\mathrm{num}}\ Q_{\mathrm{stride}}\ \mathrm{gainLog}\ \mathrm{stageLog}\ V_{\log}\ Q_\sigma\ P_{\min}\ \mathrm{requestedCoarse}\ \mathrm{endpoint} \le (p+2)^{\mathrm{requiredPower}}.$$
--   Here `preparedFiniteNestedSourceRequiredLog` is a real-valued budget of OpenAI, defined by a chain of OpenAI's budget functions over the slots `PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff` $= \mathrm{Fin}(\mathrm{outerDepth}+1) \times \mathrm{Fin}(\mathrm{innerDepth}+1) \times \mathrm{Fin}(\mathrm{cutoff}+1) \times \mathrm{Bool}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalRelativeEndpointBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B294` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalRelativeEndpointBounds.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B294

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra earlybasePower inputPower : ℕ)
    (constants : ℕ → ℕ) (hworkDepth : cutoff ≤ innerDepth) (hbasePower : 1 ≤ earlybasePower) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m ≤ s, ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      let Bstruct := (p + 2) ^ earlybasePower
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequiredLog q cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (p + 2) ^ requiredPower := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
