-- Prove2me | Theorems.Thm_JencovaRenyi_normingDual_existsUnique
-- name    : JencovaRenyi.normingDual_existsUnique
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:17.538815+00:00
-- url     : https://prove2.me/theorems/507f8a51-31fc-47bb-8135-4fe87accd1e5
-- title:
--   Strict convexity of $L_p(\mathcal M,\varphi)$ and the unique norming element $T_{q,\varphi}(h)$
-- statement:
--   Let $\varphi$ be a normal state, $1<p<\infty$, $1/p+1/q=1$, and $0\ne k\in L_p(\mathcal M,\varphi)$. Then
--
--   1. $L_p(\mathcal M,\varphi)$ is strictly convex: if $h\ne h'$ lie in its closed unit ball, $\|\tfrac12(h+h')\|_{p,\varphi}<1$;
--   2. there is a unique element $T_{q,\varphi}(k)$ of the unit ball of $L_q(\mathcal M,\varphi)$ with
--   $$
--   \langle T_{q,\varphi}(k), k\rangle = \|k\|_{p,\varphi}.
--   $$
--
--   The map $T_{q,\varphi}$ defines the elements $h$ and $h_0$ whose distance bounds the entropy drop in Theorem 3.14.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2, p.4) → every normal state $\varphi$, with $L_p(\mathcal M,\varphi)$ as extended to non-faithful states in §3, p.10; reason: for faithful $\varphi$ the support clause is automatic and $x \mapsto h_x$ is injective, so the statement specializes to the paper's.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - encoding: the element $T_{q,\varphi}(h)$ → the predicate `IsNormingDual S φ p q k h` with `∃!`; reason: states the defining property and its uniqueness; same element.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_IsNormingDual
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Jenčová, arXiv:1609.08462v4, §2.2, p.6: "The space `L_p(M, φ)` is strictly convex, hence for each
`0 ≠ h ∈ L_p(M, φ)`, there is a unique element `T_{q,φ}(h)` in the unit ball of `L_q(M, φ)` such
that `⟨T_{q,φ}(h), h⟩ = ‖h‖_{p,φ}`", for `1 < p < ∞`, `1/p + 1/q = 1`. Stated for every normal
state `φ`. Both claims are stated: strict convexity of `L_p(M, φ)` (for `h ≠ k` in its closed unit
ball, `‖½(h + k)‖_{p,φ} < 1`), and the existence and uniqueness of `T_{q,φ}(k)`. -/
theorem normingDual_existsUnique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (p q : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ = 1)
    (k : Predual A) (hk : lpNorm S φ p k < ⊤) (hk0 : k ≠ 0) :
    (∀ h h' : Predual A, lpNorm S φ p h ≤ 1 → lpNorm S φ p h' ≤ 1 → h ≠ h' →
      lpNorm S φ p ((1 / 2 : ℂ) • (h + h')) < 1) ∧
    ∃! h : Predual A, IsNormingDual S φ p q k h := by sorry

end JencovaRenyi
