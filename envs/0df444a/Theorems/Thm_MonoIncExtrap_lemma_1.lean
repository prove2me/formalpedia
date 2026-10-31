-- Prove2me | Theorems.Thm_MonoIncExtrap_lemma_1
-- name    : MonoIncExtrap.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:14.321323+00:00
-- url     : https://prove2.me/theorems/1aa234f3-4f47-4139-a262-1e121ae76dd5
-- title:
--   Lemma 1, p.5 — $F$ is Lipschitz on $\mathcal S$ and on $\widehat{\mathcal S}$
-- statement:
--   Assume the standing assumptions of §2: $\gamma_0>0$, $\delta\in(0,1)$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\epsilon>0$, $x^0\in\mathrm{dom}\,B$, Assumption 1 with $\mu>0$, and let $x^*$ be the solution of (1). Let $r_0=\|x^0-x^*\|$ and
--   $$
--   \mathcal S=\Bigl\{x\in\mathrm{dom}\,B:\|x-x^*\|\le\frac{r_0}{\sqrt{1-2\nu^2}}\Bigr\}.
--   $$
--   Then $F$ is $L_{\mathcal S}$-Lipschitz on $\mathcal S$ for some $L_{\mathcal S}>0$, and $F$ is $L_{\widehat{\mathcal S}}$-Lipschitz, for some $L_{\widehat{\mathcal S}}>0$, on
--   $$
--   \widehat{\mathcal S}=\Bigl\{x\in\mathrm{dom}\,B:\|x-x^*\|\le\frac{(5+9\gamma_0L_{\mathcal S})r_0}{3\sqrt{1-2\nu^2}}\Bigr\}.
--   $$
--
--   This turns the local Lipschitz assumption into two usable global constants on bounded sets.
--
--   **Formalization Note** `ValidS` packages the two constants and their bounds; $\widehat{\mathcal S}$ is built from $L_{\mathcal S}$, so they form a dependent pair.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Lemma 1, p.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Lemma 1.** arXiv:2206.00973v3, Lemma 1, p.5. Under the standing assumptions of §2, `F` is
`L_S`-Lipschitz continuous on `S` of (8) for some `L_S > 0`, and `F` is `L_Ŝ`-Lipschitz continuous
on `Ŝ` of (10), built from that `L_S`, for some `L_Ŝ > 0`.

**Formalization Note.** `ValidS` carries both positivities and both Lipschitz bounds; the two
constants are a dependent pair because `Ŝ` depends on `L_S`. -/
theorem lemma_1 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg1.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg1.Standing B I xstar) :
    ∃ LS LShat : ℝ, Alg1.ValidS B I xstar LS LShat := by sorry

end MonoIncExtrap
