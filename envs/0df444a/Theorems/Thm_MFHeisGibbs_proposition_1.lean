-- Prove2me | Theorems.Thm_MFHeisGibbs_proposition_1
-- name    : MFHeisGibbs.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:59.275203+00:00
-- url     : https://prove2.me/theorems/4369479e-aad1-4a1c-bb27-34e6519fdb77
-- title:
--   Proposition 1 — $c_\star\mathcal E_{DM}\le\mathcal E_C\le\mathcal E_{DM}$ on $\mathrm{comm}\{H_n\}$
-- statement:
--   Let $f$ satisfy (4), $n\ge2$ and $\beta\ge0$. For all $X\in\mathrm{comm}\{H_n\}$,
--
--   $$c_\star\mathcal E_{DM}(X)\le\mathcal E_C(X)\le\mathcal E_{DM}(X),$$
--
--   and for $V\in\{R_n,P_n\}$, $c_\star\gamma(\mathcal L_{DM},V)\le\gamma(\mathcal L_C,V)\le\gamma(\mathcal L_{DM},V)$.
--
--   On the commutant, the coherent generator is therefore equivalent to the Davies–Metropolis one, whose gap is known.
--
--   Differences from the source:
--   - encoding: γ(L_C, V) = Θ(γ(L_DM, V)) → the two-sided bound with constants c⋆ and 1; reason: this is the meaning of Θ in the page's proof, with its constants; c⋆ and 1 do not depend on n
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Proposition 1, p.8 (PDF 9); again p.14 (PDF 15)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Proposition 1 (Gap equivalence for commuting operators)**, Raikovich, Mák, Czabán, Gilyén,
arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.8 (again p.14). For `n ≥ 2`, `β ≥ 0`: `c⋆ E_DM(X) ≤ E_C(X) ≤ E_DM(X)` on `comm({H_n})`, and
consequently `γ(L_C, R_n) = Θ(γ(L_DM, R_n))`, `γ(L_C, P_n) = Θ(γ(L_DM, P_n))`.

**Formalization Note.** The two `Θ` are stated with the constants the page's inequality gives:
`c⋆ γ(L_DM, V) ≤ γ(L_C, V) ≤ γ(L_DM, V)`. -/
theorem proposition_1 (f : ℝ → ℂ) (hf : IsKMSFilter f) (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (hn : 2 ≤ n) :
    (∀ X ∈ commH n,
      cStar f * dirichlet β (LDM β n) X ≤ dirichlet β (LC β f n) X ∧
        dirichlet β (LC β f n) X ≤ dirichlet β (LDM β n) X) ∧
    (∀ V ∈ ({Rn n, Pn n} : Set (Set (Op n))),
      cStar f * sectorGap β (LDM β n) V ≤ sectorGap β (LC β f n) V ∧
        sectorGap β (LC β f n) V ≤ sectorGap β (LDM β n) V) := by sorry

end MFHeisGibbs
