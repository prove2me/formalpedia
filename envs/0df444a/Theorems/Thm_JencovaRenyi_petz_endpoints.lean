-- Prove2me | Theorems.Thm_JencovaRenyi_petz_endpoints
-- name    : JencovaRenyi.petz_endpoints
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:11.041084+00:00
-- url     : https://prove2.me/theorems/84bb767d-ecb2-44a1-b5ce-e163cec08c54
-- title:
--   §3.3 — $\Phi$ maps $L_1(\mathcal M,\varphi)$ and $L_\infty(\mathcal M,\varphi)$ into their $\mathcal N$ counterparts; the map $\Phi^*_\varphi$
-- statement:
--   Let $\Phi : L_1(\mathcal M)\to L_1(\mathcal N)$ be positive, linear and trace preserving, $\varphi$ a normal state on $\mathcal M$, $e = s(\varphi)$, $e' = s(\Phi(\varphi))$. Then
--
--   1. $\Phi$ maps $L_1(\mathcal M,\varphi)$ into $L_1(\mathcal N,\Phi(\varphi))$: if $k = eke$ then $\Phi(k) = e'\Phi(k)e'$;
--   2. $\Phi$ maps $L_\infty(\mathcal M,\varphi)$ into $L_\infty(\mathcal N,\Phi(\varphi))$: for every $x\in\mathcal M$ there is $x'\in\mathcal N$ with $\Phi(h_x) = \Phi(h_\varphi)^{1/2}x'\,\Phi(h_\varphi)^{1/2}$;
--   3. $x\mapsto x'$ extends to a linear map $\Phi^*_\varphi : e\mathcal Me\to e'\mathcal Ne'$ which is positive, unital and normal. Precisely: there is a linear $\Theta:\mathcal M\to\mathcal N$ ($\Theta(x) = \Phi^*_\varphi(exe)$) with $\Phi(h_x) = \Phi(h_\varphi)_{\Theta(x)}$ and $\Theta(x) = \Theta(1)\Theta(x)\Theta(1)$ for all $x$, $\Theta(x)\ge0$ for $x\ge0$, $\omega\circ\Theta$ normal for every normal $\omega$ on $\mathcal N$, and $\Theta(1) = e'$, the smallest projection $r\in\mathcal N$ with $\Phi(\varphi)(r) = 1$.
--
--   $\Phi^*_\varphi$ is the dual of the Petz map; the endpoint statements feed the interpolation argument of Proposition 3.12.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - encoding: $\Phi : L_1(\mathcal M) \to L_1(\mathcal N)$ positive, linear, trace preserving (p.16) → a complex-linear `Φ : Predual A →ₗ[ℂ] Predual B` with `IsPositiveTP Φ` (positive functionals to positive functionals, $(\Phi\psi)(1) = \psi(1)$); reason: p.16 itself reads $\Phi$ as the map $\mathcal M_* \to \mathcal N_*$; Lean convention.
--   - encoding: the support projections $e, e'$ and $\Phi^*_\varphi : e\mathcal Me\to e'\mathcal Ne'$ → a linear $\Theta:\mathcal M\to\mathcal N$ with $\Theta(x)\in\Theta(1)\mathcal N\Theta(1)$ and $\Theta(1)$ the least projection of $\Phi(\varphi)$-measure $1$; supports of functionals via `IsSupported`; reason: Mathlib has no support projection; $\Theta$ restricted to $e\mathcal Me$ is $\Phi^*_\varphi$, and $\Theta(x) = \Phi^*_\varphi(exe)$ is determined by these properties.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §3.3, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_IsPositiveTP
import Definitions.Def_JencovaRenyi_IsPetzDual
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Jenčová, arXiv:1609.08462v4, §3.3, p.16. Let `Φ : L_1(M) → L_1(N)` be positive, linear and trace
preserving, `φ` a normal state, `e = s(φ)`, `e' = s(Φ(φ))`. Then

1. `Φ` maps `L_1(M, φ)` into `L_1(N, Φ(φ))`;
2. `Φ` maps `L_∞(M, φ)` into `L_∞(N, Φ(φ))`: for every `x ∈ M` there is `x' ∈ N` with
   `Φ(h_x) = Φ(h_φ)_{x'}`;
3. the map `x ↦ x'` extends to a linear map `Φ*_φ : eMe → e'Ne'`, which is positive, unital and
   normal. Without support projections: there is a linear `Θ : M → N` (`Θ(x) = Φ*_φ(exe)`) with
   `Φ(h_x) = Φ(h_φ)_{Θ(x)}`, `Θ(x) ∈ Θ(1) N Θ(1)`, `Θ(x) ≥ 0` for `x ≥ 0`, `ω ∘ Θ` normal for every
   normal `ω`, and `Θ(1) = e'`, the least projection `r ∈ N` with `Φ(φ)(r) = 1`. -/
theorem petz_endpoints {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} {B : StarSubalgebra ℂ (K →L[ℂ] K)}
    (SA : StandardForm A) (SB : StandardForm B) (Φ : Predual A →ₗ[ℂ] Predual B)
    (hΦ : IsPositiveTP Φ) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ)) :
    (∀ k : Predual A, IsSupported φ k → IsSupported (Φ φ) (Φ k)) ∧
    (∀ x : A, ∃ y : B, IsPetzPair SA SB Φ φ x y) ∧
    ∃ Θ : A →ₗ[ℂ] B,
      (∀ x : A, IsPetzPair SA SB Φ φ x (Θ x)) ∧
      (∀ x : A, Θ x = Θ 1 * Θ x * Θ 1) ∧
      (∀ x : A, 0 ≤ (x : H →L[ℂ] H) → 0 ≤ ((Θ x : B) : K →L[ℂ] K)) ∧
      (∀ ω : Predual B, ∃ ω' : Predual A,
        ∀ x : A, (ω' : A →L[ℂ] ℂ) x = (ω : B →L[ℂ] ℂ) (Θ x)) ∧
      IsStarProjection (Θ 1) ∧ ((Φ φ : Predual B) : B →L[ℂ] ℂ) (Θ 1) = 1 ∧
      ∀ r : B, IsStarProjection r → ((Φ φ : Predual B) : B →L[ℂ] ℂ) r = 1 →
        ((Θ 1 : B) : K →L[ℂ] K) ≤ (r : K →L[ℂ] K) := by sorry

end JencovaRenyi
