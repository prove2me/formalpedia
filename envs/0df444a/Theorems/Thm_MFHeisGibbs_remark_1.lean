-- Prove2me | Theorems.Thm_MFHeisGibbs_remark_1
-- name    : MFHeisGibbs.remark_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:23.946517+00:00
-- url     : https://prove2.me/theorems/03e7f88f-dab5-4532-a6f7-bc559bd25b39
-- title:
--   Remark 1, (44) — $c_\star\mathcal E_{DM}\le\mathcal E_D\le\mathcal E_{DM}$ on all of $B(\mathcal H_n)$
-- statement:
--   Let $f$ satisfy (4), $n\ge2$ and $\beta\ge0$. For all $X\in B(\mathcal H_n)$,
--
--   $$c_\star\mathcal E_{DM}(X)\le\mathcal E_D(X)\le\mathcal E_{DM}(X),$$
--
--   and $c_\star\gamma(\mathcal L_{DM})\le\gamma(\mathcal L_D)\le\gamma(\mathcal L_{DM})$.
--
--   This extends the phase diagram from Metropolis weights to a general Davies generator.
--
--   Differences from the source:
--   - encoding: γ(L_D) = Θ(γ(L_DM)) → the two-sided bound with constants c⋆ and 1, for the spectral gap; reason: this is what (44) gives with the page's constants
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Remark 1, p.9 (PDF 10); (44), p.14 (PDF 15)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Remark 1 (Gap of a Davies generator with general KMS-symmetric `f`)**, with (44), Raikovich, Mák,
Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.9 (again p.14). `c⋆ E_DM(X) ≤ E_D(X) ≤ E_DM(X)` for all `X`, and
`γ(L_D) = Θ(γ(L_DM))`.

**Formalization Note.** The `Θ` is stated with the constants of (44): `c⋆ γ(L_DM) ≤ γ(L_D) ≤ γ(L_DM)`,
for the spectral gap. -/
theorem remark_1 (f : ℝ → ℂ) (hf : IsKMSFilter f) (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (hn : 2 ≤ n) :
    (∀ X : Op n,
      cStar f * dirichlet β (LDM β n) X ≤ dirichlet β (LD β f n) X ∧
        dirichlet β (LD β f n) X ≤ dirichlet β (LDM β n) X) ∧
    cStar f * specGap (LDM β n) ≤ specGap (LD β f n) ∧
      specGap (LD β f n) ≤ specGap (LDM β n) := by sorry

end MFHeisGibbs
