-- Prove2me | Theorems.Thm_GL2QFT_lemma_A_4
-- name    : GL2QFT.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:34.235407+00:00
-- url     : https://prove2.me/theorems/01d41e84-1d74-4c6c-9674-f8175021c33b
-- title:
--   Lemma A.4 — Gauss sum identities (267)–(270) and $|g_{q^2}(\theta)|=q$
-- statement:
--   For $\alpha,\beta\in X_q$ and $b\in\mathbb F_q^*$:
--   $$G_q(\alpha,b)=\chi_{\alpha^{-1}}(b)\,g_q(\alpha),\qquad \overline{g_q(\alpha)}=\chi_\alpha(-1)\,g_q(\alpha^{-1}),$$
--   $$g_q(\alpha)g_q(\beta)=J(\alpha,\beta)\,g_q(\alpha\beta)\quad(\alpha\beta\neq1),\qquad g_q(1)=-1,\qquad |g_q(\alpha)|=\sqrt q\quad(\alpha\neq1),$$
--   where $J(\alpha,\beta)=\sum_{x\in\mathbb F_q^*\setminus\{1\}}\chi_\alpha(x)\chi_\beta(1-x)$ is the Jacobi sum. Moreover $|g_{q^2}(\theta)|=q$ for every nontrivial character $\theta$ of $\mathbb F_{q^2}^*$.
--
--   These identities supply all the phases and normalizations of the A-matrix and of the torus circuit of §6.5.
--
--   Differences from the source:
--   - encoding: $\alpha^{-1}$, $\alpha\beta$, the trivial character $1$ → the exponent labels $-\alpha$, $\alpha+\beta$, $0$; reason: Remark 6.2
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma A.4, eqs. (267)–(270), p.79 (PDF p.80)

import Definitions.Def_GL2QFT_Characters

open Classical

namespace GL2QFT

open FieldData

open scoped ComplexConjugate

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma A.4**, p.79 (PDF p.80): "For
`α, β ∈ X_q` and `b ∈ F*_q`,
`G_q(α, b) = χ_{α⁻¹}(b) g_q(α)` (267), `conj(g_q(α)) = χ_α(−1) g_q(α⁻¹)` (268),
`g_q(α) g_q(β) = J(α, β) g_q(αβ)`, `αβ ≠ 1` (269),
`g_q(1) = −1`, `|g_q(α)| = √q`, `α ≠ 1` (270),
where `J(α, β) = Σ_{x ∈ F*_q ∖ {1}} χ_α(x) χ_β(1 − x)` is known as the Jacobi sum. Moreover,
`|g_{q²}(θ)| = q` for nontrivial `θ`."

Labels are exponents: `α⁻¹ = −α`, `αβ = α + β`, the trivial character "`1`" is the label `0`; `θ`
ranges over the characters `θ_k`, nontrivial iff `k ≠ 0`. The conjugation bar of (268) is on the
rendered page. -/
theorem lemma_A_4 (D : FieldData) :
    (∀ (α : D.Lab) (b : D.Fq), b ≠ 0 → D.gaussG α b = D.chi (-α) b * D.gauss α) ∧
    (∀ α : D.Lab, conj (D.gauss α) = D.chi α (-1) * D.gauss (-α)) ∧
    (∀ α β : D.Lab, α + β ≠ 0 → D.gauss α * D.gauss β = D.jacobi α β * D.gauss (α + β)) ∧
    D.gauss 0 = -1 ∧
    (∀ α : D.Lab, α ≠ 0 → ‖D.gauss α‖ = Real.sqrt D.q) ∧
    (∀ k : D.Lab2, k ≠ 0 → ‖D.gaussQ2 (D.theta k)‖ = D.q) := by sorry

end GL2QFT
