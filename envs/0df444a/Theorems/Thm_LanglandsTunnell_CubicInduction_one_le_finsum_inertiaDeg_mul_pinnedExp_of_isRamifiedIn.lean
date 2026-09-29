-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/aa3657a4-cdb3-5c91-90f8-2f31fe4ebb85
-- title:
--   Ramified places force pinned exponent sum at least one
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal{O}_K$ over $\mathcal{O}_{\mathbb{Q}}$ that is integral, let $\mu\colon (\mathbb{A}_K)^{\times}\to\mathbb{C}^{\times}$ be a homomorphism of the unit group of the adele ring of $K$ into $\mathbb{C}^{\times}$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$. Assume `IsRamifiedIn K v`, that is: there is a height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying in the fibre `primeFibre ℚ K v` (those $\mathfrak{P}$ with $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}} = v$) whose ramification index `Ideal.ramificationIdx'` over $v$ is not $1$. Then the finite sum, over the primes $w$ of $\mathcal{O}_K$ in that fibre, of $f(w/v)\cdot \mathrm{pinnedExp}\,K\,\mu\,w$ is at least $1$ as an integer, where $f(w/v)$ is `Ideal.inertiaDeg'` of $v$ in $w$ and $\mathrm{pinnedExp}\,K\,\mu\,w$ is the sum of the conductor exponent at $w$ (the infimum of the $c$ satisfying `HasConductorExponentAt`) of the local component of $\mu$ at $w$, obtained from $\mu$ by restriction along the local units, and the level `addCharLevel` of the standard local additive character $\psi_{K,w}$, namely the supremum of the integers $n$ such that $\psi_{K,w}$ is trivial on all $x$ with $|x|_w\le \exp(n)$.
--
--   The quantity bounded here is the level at $v$ of the automorphic induction attached to $\mu$, computed as a sum over the primes above $v$ of local inertia degrees times pinned exponents; the statement records that a ramified $v$ contributes at least $1$, because the different already forces a positive additive-character level. It supplies the hypothesis $1\le\ell$ in the construction of normalised new vectors at ramified places in the cubic-induction step, and is cited by the converse-theorem inputs on conductor exponents and by the level bound for cyclic subspaces of $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsRamifiedIn K v) :
    (1 : ℤ) ≤ ∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
      (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w := by sorry
