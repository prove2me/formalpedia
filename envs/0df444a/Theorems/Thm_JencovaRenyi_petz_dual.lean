-- Prove2me | Theorems.Thm_JencovaRenyi_petz_dual
-- name    : JencovaRenyi.petz_dual
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:42.598916+00:00
-- url     : https://prove2.me/theorems/c5d70270-eb7b-4b57-8007-85b830ae2b7b
-- title:
--   (16), (17) — the Petz dual $\Phi_\varphi$: adjoint of $\Phi$, $\Phi_\varphi(\Phi(h_\varphi)) = h_\varphi$, positive $L_p$ contraction
-- statement:
--   Let $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$ be positive, linear and trace preserving, $\varphi$ a normal state on $\mathcal M$, and $\Phi_\varphi$ the preadjoint of $\Phi^*_\varphi$ (defined by (16)).
--
--   1. For every $h_0\in L_1(\mathcal N,\Phi(\varphi))$ the element $\Phi_\varphi(h_0)$ exists and is unique.
--   2. (17): for $1\le p\le\infty$, $1/p+1/q=1$, $h\in L_p(\mathcal M,\varphi)$ and $h_0\in L_q(\mathcal N,\Phi(\varphi))$,
--   $$
--   \langle h_0,\Phi(h)\rangle = \langle\Phi_\varphi(h_0), h\rangle .
--   $$
--   3. $\Phi_\varphi(\Phi(h_\varphi)) = h_\varphi$.
--   4. $\Phi_\varphi$ is a positive contraction $L_p(\mathcal N,\Phi(\varphi))\to L_p(\mathcal M,\varphi)$ for $1\le p\le\infty$.
--
--   $\Phi_\varphi$ is the Petz recovery map; Theorem 3.14 measures the entropy drop by how far it is from inverting $\Phi$ on the norming dual of $h_\psi$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - encoding: $\Phi : L_1(\mathcal M) \to L_1(\mathcal N)$ positive, linear, trace preserving (p.16) → a complex-linear `Φ : Predual A →ₗ[ℂ] Predual B` with `IsPositiveTP Φ` (positive functionals to positive functionals, $(\Phi\psi)(1) = \psi(1)$); reason: p.16 itself reads $\Phi$ as the map $\mathcal M_* \to \mathcal N_*$; Lean convention.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - encoding: the map $\Phi_\varphi$ (preadjoint of $\Phi^*_\varphi$) → the predicate `IsPetzDual SA SB Φ φ h₀ g` ($g = ege$, $g(x) = h_0(y)$ for every pair with $\Phi(h_x) = \Phi(h_\varphi)_y$), with existence and uniqueness as clause 1; reason: the preadjoint is characterized by (16); same map.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §3.3, (16), (17), p.16

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_pairing
import Definitions.Def_JencovaRenyi_IsPositiveTP
import Definitions.Def_JencovaRenyi_IsPetzDual
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- (16), (17) and the closing claims of §3.3, Jenčová, arXiv:1609.08462v4, p.16. Let
`Φ : L_1(M) → L_1(N)` be positive, linear and trace preserving, `φ` a normal state, and
`Φ_φ` the preadjoint of `Φ*_φ`.

1. `Φ_φ(h₀)` exists and is unique for every `h₀ ∈ L_1(N, Φ(φ))` ((16)).
2. (17): `⟨h₀, Φ(h)⟩ = ⟨Φ_φ(h₀), h⟩` for `h ∈ L_p(M, φ)`, `h₀ ∈ L_q(N, Φ(φ))`, `1 ≤ p ≤ ∞`,
   `1/p + 1/q = 1`.
3. `Φ_φ(Φ(h_φ)) = h_φ`.
4. `Φ_φ` is a positive contraction `L_p(N, Φ(φ)) → L_p(M, φ)` for `1 ≤ p ≤ ∞`. -/
theorem petz_dual {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (hΦ : IsPositiveTP Φ) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ)) :
    (∀ h₀ : Predual B, IsSupported (Φ φ) h₀ → ∃! g : Predual A, IsPetzDual SA SB Φ φ h₀ g) ∧
    (∀ p q : ℝ≥0∞, 1 ≤ p → p⁻¹ + q⁻¹ = 1 → ∀ (h₀ : Predual B) (g : Predual A),
      IsPetzDual SA SB Φ φ h₀ g → lpNorm SB (Φ φ) q h₀ < ⊤ →
      ∀ h : Predual A, lpNorm SA φ p h < ⊤ →
        pairing SB (Φ φ) q h₀ (Φ h) = pairing SA φ q g h) ∧
    IsPetzDual SA SB Φ φ (Φ φ) φ ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ (h₀ : Predual B) (g : Predual A), IsPetzDual SA SB Φ φ h₀ g →
      lpNorm SA φ p g ≤ lpNorm SB (Φ φ) p h₀) ∧
    (∀ (h₀ : Predual B) (g : Predual A), IsPetzDual SA SB Φ φ h₀ g → IsPositive h₀ →
      IsPositive g) := by sorry

end JencovaRenyi
