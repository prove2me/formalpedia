-- Prove2me | Theorems.Thm_MFHeisGibbs_lemma_14
-- name    : MFHeisGibbs.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:29.226148+00:00
-- url     : https://prove2.me/theorems/c07854b7-19b4-48ec-b670-650a4b5e78d8
-- title:
--   Lemma 14, (70), (71) — the Casimir $C_{\mathrm{ad}}$ has spectrum in $\{\ell(\ell+1)\}$ and gap $2$ on $R_n^\perp$
-- statement:
--   Let $\beta\ge0$, $n\ge2$ and $C_{\mathrm{ad}}[\cdot]=\sum_\alpha[S^\alpha_{\mathrm{tot}},[S^\alpha_{\mathrm{tot}},\cdot]]$. Then $C_{\mathrm{ad}}$ is KMS-self-adjoint and positive semidefinite, with
--
--   $$\langle X,C_{\mathrm{ad}}[X]\rangle_\rho=\sum_\alpha\|[S^\alpha_{\mathrm{tot}},X]\|_\rho^2,$$
--
--   $\ker C_{\mathrm{ad}}=R_n$, and every eigenvalue lies in $\{\ell(\ell+1):\ell\in\mathbb Z_{\ge0}\}$. The complement $R_n^\perp$ is invariant, every eigenvalue on it is at least $2$, and $\sum_\alpha\|[S^\alpha_{\mathrm{tot}},X]\|_\rho^2\ge2\|X\|_\rho^2$ for $X\in R_n^\perp$.
--
--   The constant $2$ does not depend on $n$ or $\beta$.
--
--   Differences from the source:
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Lemma 14, (70), (71), p.27 (PDF 28)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

namespace MFHeisGibbs

/-- **Lemma 14 (Casimir spectral bound)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.27.
`C_ad` is KMS-self-adjoint and positive semidefinite, with form (70); `ker C_ad = R_n`; every eigenvalue
lies in `{ℓ(ℓ+1) : ℓ ∈ ℤ_{≥0}}`; `R_n^⊥` is invariant with every eigenvalue there at least `2`; and (71). -/
theorem lemma_14 (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (hn : 2 ≤ n) :
    (∀ X Y : Op n, kmsInner β X (Cad n Y) = kmsInner β (Cad n X) Y) ∧
    (∀ X : Op n, 0 ≤ (kmsInner β X (Cad n X)).re ∧ (kmsInner β X (Cad n X)).im = 0) ∧
    (∀ X : Op n, kmsInner β X (Cad n X) =
      ((∑ α : Fin 3, kmsNormSq β (comm (Stot n α) X) : ℝ) : ℂ)) ∧
    (∀ X : Op n, Cad n X = 0 ↔ X ∈ Rn n) ∧
    (∀ (l : ℂ) (X : Op n), X ≠ 0 → Cad n X = l • X → ∃ m : ℕ, l = ((m : ℂ) * ((m : ℂ) + 1))) ∧
    (∀ X ∈ hsPerp (Rn n), Cad n X ∈ hsPerp (Rn n)) ∧
    (∀ (l : ℂ) (X : Op n), X ∈ hsPerp (Rn n) → X ≠ 0 → Cad n X = l • X → l.im = 0 ∧ 2 ≤ l.re) ∧
    (∀ X ∈ hsPerp (Rn n), 2 * kmsNormSq β X ≤ ∑ α : Fin 3, kmsNormSq β (comm (Stot n α) X)) := by sorry

end MFHeisGibbs
