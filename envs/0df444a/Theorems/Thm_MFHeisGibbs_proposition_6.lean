-- Prove2me | Theorems.Thm_MFHeisGibbs_proposition_6
-- name    : MFHeisGibbs.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:26.684237+00:00
-- url     : https://prove2.me/theorems/98c0dc01-9565-4e63-9bba-a21d5fdcc75e
-- title:
--   Proposition 6, (135) — $\mathcal E_{\mathcal L_{F,\sigma}}(M_z)\le n$ and $\gamma(\mathcal L_{F,\sigma})\le n/\mathrm{Var}_\rho(M_z)$
-- statement:
--   Let $0<\beta<\infty$, $\sigma>0$, $f$ satisfy (4), $n\ge2$ and $M_z=S^z_{\mathrm{tot}}$. Then
--
--   $$\mathcal E_{\mathcal L_{F,\sigma}}(M_z)\le n,\qquad\gamma(\mathcal L_{F,\sigma})\le\frac{n}{\mathrm{Var}_\rho(M_z)} .$$
--
--   This is the upper bound for the OFT generator, by testing on the magnetization.
--
--   Differences from the source:
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Proposition 6, (135), p.56 (PDF 57)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Proposition 6 (OFT gap upper bound)**, (135), Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.56. Under the
assumptions of Corollary 6, with `M_z = S^z_tot`: `E_{L_{F,σ}}(M_z) ≤ n`, `γ(L_{F,σ}) ≤ n/Var_ρ(M_z)`. -/
theorem proposition_6 (f : ℝ → ℂ) (hf : IsKMSFilter f) (β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (hn : 2 ≤ n) :
    dirichlet β (LF β s f n) (Stot n 2) ≤ (n : ℝ) ∧
    specGap (LF β s f n) ≤ (n : ℝ) / gibbsVar β (Stot n 2) := by sorry

end MFHeisGibbs
