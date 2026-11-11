-- Prove2me | Theorems.Thm_GL2QFT_lemma_A_5
-- name    : GL2QFT.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:11.637877+00:00
-- url     : https://prove2.me/theorems/c91512ff-ee8d-4410-9ca1-81daf00db955
-- title:
--   Lemma A.5 — trace-fibre sums $S_t(\theta)$ and the decomposition of $g_{q^2}(\theta)$
-- statement:
--   Let $\theta$ be a character of $\mathbb F_{q^2}^*$ with $\theta|_{\mathbb F_q^*}=\chi_\alpha$, and for $t\in\mathbb F_q$ put
--   $$S_t(\theta)=\sum_{z\in\mathbb F_{q^2}^*,\ \mathrm{tr}(z)=t}\theta(z).$$
--   Then $S_t(\theta)=\chi_\alpha(t)S_1(\theta)$ for $t\in\mathbb F_q^*$, and $g_{q^2}(\theta)=S_0(\theta)+g_q(\alpha)S_1(\theta)$. If $\zeta\in\mathbb F_{q^2}^*$ has $\mathrm{tr}(\zeta)=0$, then $S_0(\theta)=0$ for $\alpha\neq1$ and $S_0(\theta)=(q-1)\theta(\zeta)$ for $\alpha=1$. If moreover $\theta\neq1$ and $\alpha=1$, then $S_1(\theta)=-\theta(\zeta)$ and $g_{q^2}(\theta)=q\,\theta(\zeta)$.
--
--   The lemma converts Gauss sums over $\mathbb F_{q^2}$ into sums over trace fibres. It is used for the cuspidal coefficients of the A-block (Lemmas 6.24–6.25).
--
--   Differences from the source:
--   - encoding: $\theta\in X_{q^2}$, "write $\theta|_{\mathbb F_q^*}=\chi_\alpha$" → $\theta=\theta_k$ with the hypothesis $\theta_k(x)=\chi_\alpha(x)$ for all $x\in\mathbb F_q^*$; the trivial character $1$ → label $0$; reason: Remark 6.2 and Appendix A labels
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma A.5, eqs. (271)–(274), p.80 (PDF p.81)

import Definitions.Def_GL2QFT_Characters

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma A.5**, p.80 (PDF p.81): "Let
`θ ∈ X_{q²}`, and write `θ|_{F*_q} = χ_α`. For `t ∈ F_q`, set `S_t(θ) := Σ_{z ∈ F*_{q²}, tr(z) = t} θ(z)`
(271). Then `S_t(θ) = χ_α(t) S_1(θ)` (`t ∈ F*_q`), `g_{q²}(θ) = S_0(θ) + g_q(α) S_1(θ)` (272). If
`ζ ∈ F*_{q²}` has `tr(ζ) = 0`, then `S_0(θ) = 0` if `α ≠ 1`; `(q − 1)θ(ζ)` if `α = 1` (273).
Moreover, if `θ ≠ 1` and `α = 1`, then `S_1(θ) = −θ(ζ)`, `g_{q²}(θ) = qθ(ζ)` (274)."

`θ = θ_k`; the hypothesis `θ_k(x) = χ_α(x)` for `x ∈ F*_q ⊂ F*_{q²}` is "`θ|_{F*_q} = χ_α`"; the
trivial character "`1`" is the label `0`. -/
theorem lemma_A_5 (D : FieldData) (k : D.Lab2) (α : D.Lab)
    (hres : ∀ x : D.Fq, x ≠ 0 → D.theta k (algebraMap D.Fq D.Fq2 x) = D.chi α x) :
    let S : D.Fq → ℂ := fun t =>
      ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t), D.theta k z
    (∀ t : D.Fq, t ≠ 0 → S t = D.chi α t * S 1) ∧
    D.gaussQ2 (D.theta k) = S 0 + D.gauss α * S 1 ∧
    (∀ ζ : D.Fq2, ζ ≠ 0 → D.tr ζ = 0 →
      S 0 = if α = 0 then ((D.q : ℂ) - 1) * D.theta k ζ else 0) ∧
    (k ≠ 0 → α = 0 → ∀ ζ : D.Fq2, ζ ≠ 0 → D.tr ζ = 0 →
      S 1 = -D.theta k ζ ∧ D.gaussQ2 (D.theta k) = (D.q : ℂ) * D.theta k ζ) := by sorry

end GL2QFT
