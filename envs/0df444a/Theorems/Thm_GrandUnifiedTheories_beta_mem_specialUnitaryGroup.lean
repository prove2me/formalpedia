-- Prove2me | Theorems.Thm_GrandUnifiedTheories_beta_mem_specialUnitaryGroup
-- name    : GrandUnifiedTheories.beta_mem_specialUnitaryGroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:51:59.002489+00:00
-- url     : https://prove2.me/theorems/d3138993-543e-4867-a979-a524ecf008fb
-- title:
--   $\beta$ maps $G_{\mathrm{SM}}$ into $\mathrm{SU}(2)\times\mathrm{SU}(2)\times\mathrm{SU}(4)$
-- statement:
--   For every $x = (\alpha, g, h)$ in the Standard Model gauge group, the triple
--
--   $$\beta(x) \;=\; \left(g,\;\begin{pmatrix}\alpha^{3}&0\\0&\alpha^{-3}\end{pmatrix},\;\begin{pmatrix}\alpha h&0\\0&\alpha^{-3}\end{pmatrix}\right)$$
--
--   lies in the Pati-Salam group $\mathrm{SU}(2)\times\mathrm{SU}(2)\times\mathrm{SU}(4)$: each of the three matrices is unitary with determinant one.
--
--   The determinants are $\det g = 1$, $\alpha^{3}\alpha^{-3} = 1$, and $\alpha^{3}\det h\cdot\alpha^{-3} = 1$. The exponents are fixed by the requirement that pulling the Pati-Salam representation back along $\beta$ reproduce the Standard Model hypercharges: the colour part $\mathbb{C}^3\subset\mathbb{C}^4$ must transform with hypercharge $\tfrac13$ and the lepton part $\mathbb{C}$ with hypercharge $-1$.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 3.3, p. 54 (the displayed map β : U(1) × SU(2) × SU(3) → SU(2) × SU(2) × SU(4)), together with the U(1) ⊆ SU(4) computation α³β = 1 on p. 50

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

theorem beta_mem_specialUnitaryGroup (x : GSM) :
    (betaMatrix x).1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      (betaMatrix x).2.1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      (betaMatrix x).2.2 ∈ Matrix.specialUnitaryGroup Idx4 ℂ := by sorry

end GrandUnifiedTheories
