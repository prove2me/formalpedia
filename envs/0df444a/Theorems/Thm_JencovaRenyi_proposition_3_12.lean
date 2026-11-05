-- Prove2me | Theorems.Thm_JencovaRenyi_proposition_3_12
-- name    : JencovaRenyi.proposition_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:54.896999+00:00
-- url     : https://prove2.me/theorems/6ac70b6a-aacd-4101-bb0e-47025aa9bcde
-- title:
--   Proposition 3.12 — $\Phi$ is a contraction $L_p(\mathcal M,\varphi)\to L_p(\mathcal N,\Phi(\varphi))$
-- statement:
--   Let $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$ be positive, linear and trace preserving and $\varphi$ a normal state on $\mathcal M$. For every $1\le p\le\infty$, $\Phi$ restricts to a contraction $L_p(\mathcal M,\varphi)\to L_p(\mathcal N,\Phi(\varphi))$:
--   $$
--   \|\Phi(k)\|_{p,\Phi(\varphi)}\le\|k\|_{p,\varphi}\qquad(k\in L_1(\mathcal M)).
--   $$
--   With $k = h_\psi$ and $p = \alpha$ this is the data processing inequality $\tilde D_\alpha(\Phi(\psi)\|\Phi(\varphi))\le\tilde D_\alpha(\psi\|\varphi)$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - encoding: $\Phi : L_1(\mathcal M) \to L_1(\mathcal N)$ positive, linear, trace preserving (p.16) → a complex-linear `Φ : Predual A →ₗ[ℂ] Predual B` with `IsPositiveTP Φ` (positive functionals to positive functionals, $(\Phi\psi)(1) = \psi(1)$); reason: p.16 itself reads $\Phi$ as the map $\mathcal M_* \to \mathcal N_*$; Lean convention.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Proposition 3.12, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_IsPositiveTP
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Proposition 3.12 of Jenčová, arXiv:1609.08462v4, p.16: for any `1 ≤ p ≤ ∞`, a positive linear
trace-preserving `Φ : L_1(M) → L_1(N)` restricts to a contraction
`L_p(M, φ) → L_p(N, Φ(φ))`, `φ` a normal state: `‖Φ(k)‖_{p,Φ(φ)} ≤ ‖k‖_{p,φ}`. -/
theorem proposition_3_12 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (hΦ : IsPositiveTP Φ) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (k : Predual A) :
    lpNorm SB (Φ φ) p (Φ k) ≤ lpNorm SA φ p k := by sorry

end JencovaRenyi
