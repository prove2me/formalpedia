-- Prove2me | Theorems.Thm_HScattered_Delsarte_orth_star_eq_star_orth
-- name    : HScattered.Delsarte.orth_star_eq_star_orth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:57.608148+00:00
-- url     : https://prove2.me/theorems/17aa8d5b-a5f8-4c5e-86e3-b8746be9bbcb
-- title:
--   §3, p. 9 — (S*)^⊥ = (S^⊥′)* for an 𝔽_q-subspace S of W
-- statement:
--   Work in the setting of §3: $\mathbb V=\Lambda\oplus\Gamma$ is a $k$-dimensional $\mathbb F_{q^n}$-space, $W$ is a $k$-dimensional $\mathbb F_q$-subspace spanning $\mathbb V$ over $\mathbb F_{q^n}$, and $\beta$ is a non-degenerate reflexive sesquilinear form on $\mathbb V$ which restricts to an $\mathbb F_q$-valued form $\beta'$ on $W$. Let $\perp$ and $\perp'$ be the orthogonal complement maps of $\beta$ and of $\beta'$. For an $\mathbb F_q$-subspace $S$ of $W$ write $S^*=\langle S\rangle_{\mathbb F_{q^n}}$. Then
--
--   $$
--   (S^*)^\perp=\big(S^{\perp'}\big)^* ,
--   $$
--
--   that is, the $\beta$-orthogonal complement of the $\mathbb F_{q^n}$-span of $S$ is the $\mathbb F_{q^n}$-span of the $\beta'$-orthogonal complement of $S$ inside $W$.
--
--   The identity transports orthogonality between the $\mathbb F_q$-subspaces of $W$ and the $\mathbb F_{q^n}$-subspaces of $\mathbb V$; it is used in display (10) of the proof of Theorem 3.3.
--
--   **Formalization Note** $S^{\perp'}$ is `D.orthW S` $=\{w\in W:\beta(w,s)=0\ \forall s\in S\}$ and $(\cdot)^\perp$ is `D.orth`, both from the `DelsarteSetting` definition. The hypothesis $S\subseteq W$ is the paper's.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 9, §3, "(S*)^⊥ = (S^⊥′)*" (unnumbered)

import Mathlib
import Definitions.Def_HScattered_Delsarte_DelsarteSetting

namespace HScattered.Delsarte

/-- §3, p. 9 of arXiv:1906.10590v2: in the setting of §3, for an `𝔽_q`-subspace `S` of `W`,
writing `S* = ⟨S⟩_{𝔽_{qⁿ}}`, one has `(S*)^⊥ = (S^{⊥′})*`, where `⊥` is taken with respect
to `β` on `𝕍` and `⊥′` with respect to its restriction `β′` to `W`. -/
theorem orth_star_eq_star_orth {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍) (S : Submodule F 𝕍) (hS : S ≤ D.W) :
    D.orth (Submodule.span K (S : Set 𝕍)) = Submodule.span K (D.orthW S : Set 𝕍) := by sorry

end HScattered.Delsarte
