-- Prove2me | Theorems.Thm_JencovaRenyi_eq_5
-- name    : JencovaRenyi.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:02.932304+00:00
-- url     : https://prove2.me/theorems/7a4c9f1d-a11e-43b8-88df-0662404be942
-- title:
--   (5) — $\|k\|_{p,\varphi}\le\|k\|_{p',\varphi}$ for $1\le p\le p'\le\infty$
-- statement:
--   Let $\varphi$ be a normal state and $1\le p\le p'\le\infty$. Then $L_{p'}(\mathcal M,\varphi)\subseteq L_p(\mathcal M,\varphi)$ and
--   $$
--   \|k\|_{p,\varphi}\le\|k\|_{p',\varphi}\qquad (k\in L_{p'}(\mathcal M,\varphi)).
--   $$
--   With norms valued in $[0,\infty]$ ($\infty$ off the space) the single inequality, for every $k\in L_1(\mathcal M)$, carries both claims. The family $L_p(\mathcal M,\varphi)$ is therefore decreasing in $p$, which is what makes $\tilde D_\alpha$ increasing in $\alpha$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2, p.4) → every normal state $\varphi$, with $L_p(\mathcal M,\varphi)$ as extended to non-faithful states in §3, p.10; reason: for faithful $\varphi$ the support clause is automatic and $x \mapsto h_x$ is injective, so the statement specializes to the paper's.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, (5), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- (5) of Jenčová, arXiv:1609.08462v4, §2.2, p.6: for `1 ≤ p ≤ p' ≤ ∞`,
`L_{p'}(M, φ) ⊆ L_p(M, φ)` and `‖k‖_{p,φ} ≤ ‖k‖_{p',φ}` for all `k ∈ L_{p'}(M, φ)`.

With the extended gauges (`⊤` off the space) the single inequality carries both claims. Stated
for every normal state `φ` (§2 fixes `φ` faithful; §3, p.10 extends to all normal states). -/
theorem eq_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (p p' : ℝ≥0∞) (hp : 1 ≤ p) (hpp' : p ≤ p') (k : Predual A) :
    lpNorm S φ p k ≤ lpNorm S φ p' k := by sorry

end JencovaRenyi
