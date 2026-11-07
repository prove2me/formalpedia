-- Prove2me | Theorems.Thm_MFHeisGibbs_lemma_20_corollary_5
-- name    : MFHeisGibbs.lemma_20_corollary_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:55.032211+00:00
-- url     : https://prove2.me/theorems/35e37b4e-a827-4373-bfb4-c7729c51ccf1
-- title:
--   Lemma 20 + Corollary 5 — $[\mathcal T'[I],H_n]=0$; the Lindbladians commute with $\Delta_{g,\pi}$
-- statement:
--   Let $n\ge2$ and $\beta\ge0$, let $f$ be continuous with the KMS relation of (4) and let $\sigma>0$. For each of the coherent, Davies and OFT constructions, $D=\mathcal T'[I]$ satisfies $[D,H_n]=0$. For $\mathcal L\in\{\mathcal L_C,\mathcal L_D,\mathcal L_{F,\sigma}\}$ and every $(g,\pi)\in SU(2)\times S_n$,
--
--   $$\mathcal L\circ\Delta_{g,\pi}=\Delta_{g,\pi}\circ\mathcal L,\qquad\mathcal L^\dagger\circ\Delta_{g,\pi}=\Delta_{g,\pi}\circ\mathcal L^\dagger .$$
--
--   This is why no coherent correction appears in the Lindbladians, and it is the source of all the invariant sectors used in the paper.
--
--   Differences from the source:
--   - encoding: Consequently C = 0 in (116), and L is of the form (3) → not stated as a separate clause; the generators are defined by form (3); reason: with [D, H_n] = 0 the correction C of (116) is a linear combination of vanishing Bohr components, so the two forms coincide
--   - encoding: L_{F,σ} at β = 0, which the page defines as a limit → LFall, which is LF0 at β = 0; reason: literal (10) is the zero map at β = 0; see the milestone eq_101_113_limits
--   - generalization: the generators of the introduction, built from a filter f satisfying all of (4) → f continuous with the KMS relation only (KMSRel), without |f| ≤ 1 or c⋆ > 0; reason: the proof (Lemma 19) uses only that the Bohr coefficients do not depend on (i, α), never the normalization; every f with (4) satisfies KMSRel, so the statement specializes to the page's
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Lemma 20, Corollary 5, p.48 (PDF 49)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Mixing

open Matrix

namespace MFHeisGibbs

/-- **Lemma 20 and Corollary 5**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.48.
`D = T′[I]` commutes with `H_n` for the coherent, Davies and OFT constructions, and
`L ∘ ∆_{g,π} = ∆_{g,π} ∘ L`, `L† ∘ ∆_{g,π} = ∆_{g,π} ∘ L†` for all `(g, π) ∈ SU(2) × S_n`.

**Formalization Note.** The generators are defined by (3), so the correction `C` of (116) never appears:
the content of "C = 0" is the commutation `[T′[I], H_n] = 0`. The filter needs only continuity and the
KMS relation. -/
theorem lemma_20_corollary_5 (f : ℝ → ℂ) (hf : KMSRel f) (s : ℝ) (hs : 0 < s) (β : ℝ) (hβ : 0 ≤ β)
    (n : ℕ) (hn : 2 ≤ n) :
    comm (Hn n) (transC (fun ν => f (β * ν)) n 1) = 0 ∧
    comm (Hn n) (transD (fun ν => ‖f (β * ν)‖ ^ 2) n 1) = 0 ∧
    comm (Hn n) (transF β s f n 1) = 0 ∧
    ∀ L ∈ ({LC β f n, LD β f n, LFall β s f n} : Set (Module.End ℂ (Op n))),
      ∀ (g : Matrix.specialUnitaryGroup Bool ℂ) (π : Equiv.Perm (Fin n)),
        L ∘ₗ Delta (g : Matrix Bool Bool ℂ) π = Delta (g : Matrix Bool Bool ℂ) π ∘ₗ L ∧
        hsAdjoint L ∘ₗ Delta (g : Matrix Bool Bool ℂ) π =
          Delta (g : Matrix Bool Bool ℂ) π ∘ₗ hsAdjoint L := by sorry

end MFHeisGibbs
