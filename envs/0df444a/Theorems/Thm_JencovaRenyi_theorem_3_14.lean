-- Prove2me | Theorems.Thm_JencovaRenyi_theorem_3_14
-- name    : JencovaRenyi.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:44.946229+00:00
-- url     : https://prove2.me/theorems/429c9fdc-ba50-4c85-9aa4-32d7bd6f23a5
-- title:
--   Theorem 3.14 — data processing inequality for $\tilde D_\alpha$ under positive trace-preserving maps, with bounds on the entropy drop
-- statement:
--   Let $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$ be a positive linear trace-preserving map between the preduals of two von Neumann algebras, $1<\alpha<\infty$, $1/\alpha+1/\beta = 1$, and $\psi,\varphi$ normal states on $\mathcal M$. Then
--   $$
--   \tilde D_\alpha(\Phi(\psi)\|\Phi(\varphi))\le\tilde D_\alpha(\psi\|\varphi).
--   $$
--   Assume moreover $h_\psi\in L_\alpha(\mathcal M,\varphi)$. Then $\Phi(h_\psi)\in L_\alpha(\mathcal N,\Phi(\varphi))$; let $h := T_{\beta,\varphi}(h_\psi)$, $h_0 := T_{\beta,\Phi(\varphi)}(\Phi(h_\psi))$, and $\Phi_\varphi(h_0)\in L_\beta(\mathcal M,\varphi)$ its Petz dual. Writing $\Delta = \tilde D_\alpha(\psi\|\varphi)-\tilde D_\alpha(\Phi(\psi)\|\Phi(\varphi))$:
--
--   1. for $1<\alpha\le2$,
--   $$\Delta\ge 2\,\big\|\tfrac12\big(h-\Phi_\varphi(h_0)\big)\big\|_{\beta,\varphi}^{\beta};$$
--   2. for $2\le\alpha<\infty$,
--   $$\Delta\ge \beta(\beta-1)\,\big\|\tfrac12\big(h-\Phi_\varphi(h_0)\big)\big\|_{\beta,\varphi}^{2};$$
--   3. if $\|h-\Phi_\varphi(h_0)\|_{\beta,\varphi}<1$,
--   $$\Delta\le-\beta\log\big(1-\|h-\Phi_\varphi(h_0)\|_{\beta,\varphi}\big).$$
--
--   Only positivity of $\Phi$ is needed (no complete positivity), and neither $\varphi$ nor $\Phi(\varphi)$ need be faithful. The bounds quantify how far $\Phi$ is from being sufficient for $\{\psi,\varphi\}$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - encoding: $\Phi : L_1(\mathcal M) \to L_1(\mathcal N)$ positive, linear, trace preserving (p.16) → a complex-linear `Φ : Predual A →ₗ[ℂ] Predual B` with `IsPositiveTP Φ` (positive functionals to positive functionals, $(\Phi\psi)(1) = \psi(1)$); reason: p.16 itself reads $\Phi$ as the map $\mathcal M_* \to \mathcal N_*$; Lean convention.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - generalization: Theorem 3.14 assumes $h_\psi\in L_\alpha(\mathcal M,\varphi)$ → the inequality $\tilde D_\alpha(\Phi(\psi)\|\Phi(\varphi))\le\tilde D_\alpha(\psi\|\varphi)$ is stated without it; reason: this is item (h), p.3; it is trivial when $\tilde D_\alpha(\psi\|\varphi)=\infty$, so the theorem's case is a specialization.
--   - encoding: $h = T_{\beta,\varphi}(h_\psi)$, $h_0 = T_{\beta,\Phi(\varphi)}(\Phi(h_\psi))$ and $\Phi_\varphi(h_0)\in L_\beta(\mathcal M,\varphi)$ → witnesses `h`, `h₀`, `g` asserted to exist with `IsNormingDual`, `IsNormingDual`, `IsPetzDual` and `lpNorm SA φ β g < ⊤`; $\Phi(h_\psi)\in L_\alpha$ stated as a conclusion; reason: each object is unique with its defining property (milestones `normingDual_existsUnique`, `petz_dual`), so the existential names the paper's objects.
--   - encoding: $\tilde D_\alpha(\psi\|\varphi)-\tilde D_\alpha(\Phi(\psi)\|\Phi(\varphi))$, the $\log$ → the difference of the `EReal.toReal` of the two divergences; `Real.log`, natural logarithm; reason: both divergences are finite real numbers when $h_\psi\in L_\alpha(\mathcal M,\varphi)$ (their norms are at least the trace $1$ and finite), so the real difference is the printed one.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Theorem 3.14, p.17 (proof pp.17–18), with item (h), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_IsNormingDual
import Definitions.Def_JencovaRenyi_IsPositiveTP
import Definitions.Def_JencovaRenyi_IsPetzDual
import Definitions.Def_JencovaRenyi_renyiDiv
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Theorem 3.14 of Jenčová, arXiv:1609.08462v4, p.17, with the data processing inequality of
item (h), p.3. Let `Φ : L_1(M) → L_1(N)` be a positive linear trace-preserving map (§3.3, p.16),
`1 < α < ∞`, `1/α + 1/β = 1`, and `ψ, φ` normal states on `M`. Then
`D̃_α(Φ(ψ)‖Φ(φ)) ≤ D̃_α(ψ‖φ)`. Assume moreover `h_ψ ∈ L_α(M, φ)` and put `h := T_{β,φ}(h_ψ)`,
`h₀ := T_{β,Φ(φ)}(Φ(h_ψ))`. Then for `1 < α ≤ 2`
`D̃_α(ψ‖φ) − D̃_α(Φ(ψ)‖Φ(φ)) ≥ 2‖½(h − Φ_φ(h₀))‖^β_{β,φ}`, for `2 ≤ α < ∞`
`D̃_α(ψ‖φ) − D̃_α(Φ(ψ)‖Φ(φ)) ≥ β(β − 1)‖½(h − Φ_φ(h₀))‖²_{β,φ}`, and if
`‖h − Φ_φ(h₀)‖_{β,φ} < 1`, `D̃_α(ψ‖φ) − D̃_α(Φ(ψ)‖Φ(φ)) ≤ −β log(1 − ‖h − Φ_φ(h₀)‖_{β,φ})`.

**Formalization Note.** `h`, `h₀` and `Φ_φ(h₀)` are asserted to exist with their defining
properties (each is unique). Both divergences are finite under `h_ψ ∈ L_α(M, φ)`, so their
difference is taken in `ℝ`. -/
theorem theorem_3_14 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (hΦ : IsPositiveTP Φ) (α β : ℝ) (hα : 1 < α) (hαβ : 1 / α + 1 / β = 1)
    (ψ φ : Predual A) (hψ : IsNormalState A (ψ : A →L[ℂ] ℂ))
    (hφ : IsNormalState A (φ : A →L[ℂ] ℂ)) :
    renyiDiv SB α (Φ ψ) (Φ φ) ≤ renyiDiv SA α ψ φ ∧
    (lpNorm SA φ (ENNReal.ofReal α) ψ < ⊤ →
      lpNorm SB (Φ φ) (ENNReal.ofReal α) (Φ ψ) < ⊤ ∧
      ∃ (h : Predual A) (h₀ : Predual B) (g : Predual A),
        IsNormingDual SA φ (ENNReal.ofReal α) (ENNReal.ofReal β) ψ h ∧
        IsNormingDual SB (Φ φ) (ENNReal.ofReal α) (ENNReal.ofReal β) (Φ ψ) h₀ ∧
        IsPetzDual SA SB Φ φ h₀ g ∧ lpNorm SA φ (ENNReal.ofReal β) g < ⊤ ∧
        (α ≤ 2 →
          2 * (lpNorm SA φ (ENNReal.ofReal β) ((1 / 2 : ℂ) • (h - g))).toReal ^ β ≤
            ((renyiDiv SA α ψ φ).toReal - (renyiDiv SB α (Φ ψ) (Φ φ)).toReal)) ∧
        (2 ≤ α →
          β * (β - 1) * (lpNorm SA φ (ENNReal.ofReal β) ((1 / 2 : ℂ) • (h - g))).toReal ^ (2 : ℕ) ≤
            ((renyiDiv SA α ψ φ).toReal - (renyiDiv SB α (Φ ψ) (Φ φ)).toReal)) ∧
        (lpNorm SA φ (ENNReal.ofReal β) (h - g) < 1 →
          ((renyiDiv SA α ψ φ).toReal - (renyiDiv SB α (Φ ψ) (Φ φ)).toReal) ≤
            -β * Real.log (1 - (lpNorm SA φ (ENNReal.ofReal β) (h - g)).toReal))) := by sorry

end JencovaRenyi
