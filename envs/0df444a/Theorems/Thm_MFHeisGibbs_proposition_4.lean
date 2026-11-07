-- Prove2me | Theorems.Thm_MFHeisGibbs_proposition_4
-- name    : MFHeisGibbs.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:02.523441+00:00
-- url     : https://prove2.me/theorems/d715e4f0-a768-4f71-83eb-d23aff70f1b3
-- title:
--   Proposition 4 — at $\beta=2$: $\gamma(\mathcal L_{DM})=\Omega(n^{-1/2})$ and $\langle S^z_{\mathrm{tot}},S^z_{\mathrm{tot}}\rangle_\rho=\Theta(n^{3/2})$
-- statement:
--   For $\beta=2$ there are constants, independent of $n\ge2$, with
--
--   $$\gamma(\mathcal L_{DM})\ge c\,n^{-1/2},\qquad c\,n^{3/2}\le\langle S^z_{\mathrm{tot}},S^z_{\mathrm{tot}}\rangle_\rho\le C\,n^{3/2}.$$
--
--   This closes the critical case that the earlier work on the Davies generator left open.
--
--   Differences from the source:
--   - encoding: Ω(·) and Θ(·) → ∃ constants for all n ≥ 2; reason: p.41 fixes the meaning of Θ; each quantity is positive so the bounds extend to all n ≥ 2
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Proposition 4, p.8 (PDF 9); again p.30 (PDF 31)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Proposition 4 (Critical-temperature bound)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.8 (again
p.30). For `β = 2`, `γ(L_DM) = Ω(n^{−1/2})` and `⟨S^z_tot, S^z_tot⟩_ρ = Θ(n^{3/2})`. -/
theorem proposition_4 :
    (∃ c > 0, ∀ n : ℕ, 2 ≤ n → c * (n : ℝ) ^ (-(1 / 2) : ℝ) ≤ specGap (LDM 2 n)) ∧
    (∃ c > 0, ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ (3 / 2 : ℝ) ≤ kmsNormSq 2 (Stot n 2) ∧
        kmsNormSq 2 (Stot n 2) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)) := by sorry

end MFHeisGibbs
