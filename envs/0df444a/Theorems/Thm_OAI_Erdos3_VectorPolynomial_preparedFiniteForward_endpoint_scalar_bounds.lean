-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteForward_endpoint_scalar_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedFiniteForward_endpoint_scalar_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:39:15.458573+00:00
-- url     : https://prove2.me/theorems/7c50a1b5-5322-4c94-8e72-cb7fb5832f12
-- title:
--   Scalar bounds on the endpoint parameters of the prepared finite forward recursion
-- statement:
--   Let $A,C_{\mathrm{slice}},n,\mathrm{count}\in\mathbb N$, let $\mathrm{constants}\colon\mathbb N\to\mathbb N$, and let $x,\mathrm{gainLog},\mathrm{stageLog}$ be reals, with $2\le A$, $1\le C_{\mathrm{slice}}$, $C_{\mathrm{slice}}+1\le A$, $x\ge0$, $\mathrm{gainLog}\ge0$, $\mathrm{stageLog}\ge0$ and $\mathrm{count}\le x$. Put $b=$ `preparedFiniteForwardParameter A constants n x`, $p=$ `preparedFiniteForwardWork A constants n x`, $u=$ `preparedFiniteForwardModelPrecision A constants n x gainLog stageLog`, $\mathrm{cost}=b+1$ and $\mathrm{slice}=(b+C_{\mathrm{slice}})^{C_{\mathrm{slice}}}$. Then $0\le p$, $0\le u$, $0\le\mathrm{cost}$, $0\le\mathrm{slice}$, $\mathrm{cost}\le\mathrm{slice}$, $\mathrm{slice}\cdot\mathrm{count}\le p$, every real $\mathrm{chartCost}\le x$ satisfies $\mathrm{chartCost}\le\mathrm{slice}$, and $2\,\mathrm{cost}+6\le u$. Here $b$ is the value at $x$ of the polynomial $P_n\in\mathbb N[X]$ given by $P_0=X$ and $P_{m+1}=P_m+\mathrm{cap}_m+\mathrm{branch}_m+1$, where $\mathrm{work}_m=(P_m+A)^A$, $\mathrm{cap}_m=(4P_m+4\,\mathrm{work}_m+16+A)^A$, $c_m=P_m+\mathrm{cap}_m$ and $\mathrm{branch}_m=X\cdot\mathrm{cap}_m+(c_m+8)^8+(c_m+\mathrm{constants}(m))^{\mathrm{constants}(m)}$; $p$ is the value at $x$ of $(P_n+A)^A$; and $u$ is $\texttt{preparedFiniteForwardPrefixLog}\ A\ \mathrm{constants}\ n\ x+\mathrm{gainLog}+p+\mathrm{stageLog}+6$, where `preparedFiniteForwardPrefixLog A constants n x` is $\sum_{j<n}$ `preparedFiniteForwardBranch A constants j x`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedFiniteForward_endpoint_scalar_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteForwardTreeStorage.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B015` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteForwardTreeStorage.lean#L313

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B015

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_endpoint_scalar_bounds
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ)
    {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hCslice : 1 ≤ Cslice) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hgain : 0 ≤ gainLog) (hstage : 0 ≤ stageLog)
    (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A constants n x
    let p := preparedFiniteForwardWork A constants n x
    let u := preparedFiniteForwardModelPrecision A constants n x gainLog stageLog
    let cost := b + 1
    let slice := (b + Cslice) ^ Cslice
    0 ≤ p ∧ 0 ≤ u ∧ 0 ≤ cost ∧ 0 ≤ slice ∧ cost ≤ slice ∧
      slice * count ≤ p ∧ (∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice) ∧
      2 * cost + 6 ≤ u := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
