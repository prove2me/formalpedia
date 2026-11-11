-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_4_1
-- name    : InfoLossLAR.WorstCase.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:07.968209+00:00
-- url     : https://prove2.me/theorems/b8542c78-bf73-4b32-8e2a-21ae217b04ef
-- title:
--   Lemma 4.1 — the zero-fiber decomposition $(e,y)\mapsto e+Jy$ is a bijection
-- statement:
--   Let $q$ be an odd prime and $T$ a rounding matrix with chosen Smith matrices and $\ell=d-r\ge1$ (§3.1). The zero-fiber decomposition map
--   $$\Phi_T:\mathcal F_{T,0}\times\mathbb F_q^\ell\to\mathbb F_q^d,\qquad (e,y)\mapsto e+Jy,$$
--   is a bijection, and its inverse is $\Phi_T^{-1}(x)=(x-Jf_T(x),\,f_T(x))$.
--
--   Consequently a uniform $x\in\mathbb F_q^d$ splits into an independent uniform zero-fiber residual and a uniform label; this is the step that turns uniform-zero-fiber LWE samples into LAR samples (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: "its inverse is $\Phi_T^{-1}(x)=(x-Jf_T(x),f_T(x))$" → for all $x$ and $(e,y)$: $\Phi_T(e,y)=x\iff e=x-Jf_T(x)\wedge y=f_T(x)$; reason: equivalent formulation of the inverse
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 21, Lemma 4.1

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 4.1 (Zero-fiber decomposition), p. 21: with `q` an odd prime and `ℓ = d − r ≥ 1`, the
map `Φ_T : F_{T,0} × 𝔽_q^ℓ → 𝔽_q^d`, `(e, y) ↦ e + Jy`, is a bijection, and its inverse is
`x ↦ (x − J f_T(x), f_T(x))`. -/
theorem lemma_4_1 (q r d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (hℓ : r < d) :
    Function.Bijective
      (fun p : S.zeroFiber × (Fin (d - r) → ZMod q) => (p.1 : Fin d → ZMod q) + S.J.mulVec p.2) ∧
    ∀ (x : Fin d → ZMod q) (p : S.zeroFiber × (Fin (d - r) → ZMod q)),
      (p.1 : Fin d → ZMod q) + S.J.mulVec p.2 = x ↔
        ((p.1 : Fin d → ZMod q) = x - S.J.mulVec (S.fT x) ∧ p.2 = S.fT x) := by sorry

end InfoLossLAR.WorstCase
