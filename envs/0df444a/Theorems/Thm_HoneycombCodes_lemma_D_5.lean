-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_D_5
-- name    : HoneycombCodes.lemma_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:30.777582+00:00
-- url     : https://prove2.me/theorems/24104100-ffeb-447f-b2da-3501d31f4d37
-- title:
--   Lemma D.5 — the isospectral bridge to the constant-weight boundary
-- statement:
--   Let $(u,v,A)$ be an interior minimizer as in Proposition D.4 (so $(u,v)$ minimizes (127) and $A=A_\delta(u,v)<1$), and define
--
--   $$
--   \alpha=J(A),\qquad w=J(u^2),\qquad q=J(v^2),\qquad \beta=\alpha q,\qquad \gamma=(1-\alpha)q. \tag{130}
--   $$
--
--   These parameters satisfy the constant-weight range conditions (76)–(77) strictly, and
--
--   $$
--   \Phi_{CW}(\alpha,\beta,\gamma,w)=1+g(u^2)-g(A)-g(v^2),\qquad \Lambda_{\alpha,\beta,\gamma}(w)=1-\frac{2\mathcal E(u,v,A)}{A}. \tag{132–133}
--   $$
--
--   In particular the bridge lies on the exact constant-weight spectral boundary: $E_{CW}(\alpha,\beta,\gamma,w)=\delta$ (134).
--
--   **Formalization Note** "Strictly" includes $\beta>0$ and $\gamma>0$, the strict forms of the two non-strict conditions in (76).
--
--   Differences from the source:
--
--   - encoding: '(u, v) minimize (127)' → IsR2MQCMinimizer δ u v: (u, v) ∈ F_δ and Ψ_δ(u, v) ≤ Ψ_δ at every point of F_δ; reason: the definition of a minimizer of (127)
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2
--   - reading: 'satisfy the range conditions (76)–(77) strictly' → CWRange holds and moreover 0 < β and 0 < γ; reason: the only non-strict inequalities of (76)–(77) are 0 ≤ β and 0 ≤ γ; the proof shows 0 < β < α/2 and 0 < γ < (1 − α)/2
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.4, Lemma D.5, eqs. (130)–(134), p.63 (PDF 65)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_kappaCW

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma D.5** (the isospectral bridge), Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.4, p.63 (PDF 65). Let `(u, v, A)` be an
interior minimizer as in Proposition D.4 and define `α = J(A)`, `w = J(u²)`, `q = J(v²)`,
`β = αq`, `γ = (1 − α)q` (130). These parameters satisfy the constant-weight range conditions
(76)–(77) strictly, `Φ_CW(α, β, γ, w) = 1 + g(u²) − g(A) − g(v²)` (132),
`Λ_{α,β,γ}(w) = 1 − 2E(u, v, A)/A` (133), and `E_CW(α, β, γ, w) = δ` (134).

**Formalization Note.** "Interior minimizer as in Proposition D.4": `(u, v)` minimizes (127) and
`A = A_δ(u, v) < 1`. "Strictly" includes the two non-strict conditions of (76): `0 < β`, `0 < γ`. -/
theorem lemma_D_5 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (u v : ℝ)
    (hmin : IsR2MQCMinimizer δ u v) (hA : Adelta δ u v < 1) :
    let A : ℝ := Adelta δ u v
    let α : ℝ := Jmap A
    let w : ℝ := Jmap (u ^ 2)
    let q : ℝ := Jmap (v ^ 2)
    let β : ℝ := α * q
    let γ : ℝ := (1 - α) * q
    (CWRange δ α β γ w ∧ 0 < β ∧ 0 < γ) ∧
    PhiCW α β γ w = 1 + g (u ^ 2) - g A - g (v ^ 2) ∧
    LambdaCW α β γ w = 1 - 2 * Efun u v A / A ∧
    ECW α β γ w = δ := by sorry

end HoneycombCodes
