-- Prove2me | Theorems.Thm_JencovaRenyi_cone_representative
-- name    : JencovaRenyi.cone_representative
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:42.196774+00:00
-- url     : https://prove2.me/theorems/e14248c5-bdbe-4ad0-8e3b-dc3c99c7ae31
-- title:
--   Every positive normal functional has a unique representative $h_\varphi^{1/2}$ in the positive cone
-- statement:
--   Let $\mathcal M$ be a von Neumann algebra on $H$ in standard form with positive cone $P$. For every positive normal functional $\varphi\in\mathcal M_*^+$ there is exactly one vector $\xi\in P$ with
--   $$
--   \varphi(a) = \langle\xi, a\,\xi\rangle\qquad (a\in\mathcal M).
--   $$
--   This vector is $h_\varphi^{1/2}$. It makes the cone vector, and hence the symmetric embedding $x\mapsto h_x$ and all the spaces $L_p(\mathcal M,\varphi)$, well defined.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Jenčová, arXiv:1609.08462v4, §2, p.3: "For any `φ ∈ M_*^+`, `h_φ^{1/2}` is the unique vector
representative of `φ` in the positive cone `L_2(M)^+`." For a von Neumann algebra in standard form
`S`, every positive normal functional `φ` has exactly one vector `ξ` in the cone of `S` with
`φ(a) = ⟪ξ, a ξ⟫` for all `a ∈ M` (Haagerup). -/
theorem cone_representative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsPositive φ) :
    ∃! ξ : H, ξ ∈ S.cone ∧ ∀ a : A, (φ : A →L[ℂ] ℂ) a = ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ := by sorry

end JencovaRenyi
