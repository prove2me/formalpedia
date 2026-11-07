-- Prove2me | Theorems.Thm_MFHeisGibbs_lemma_3
-- name    : MFHeisGibbs.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:26.371701+00:00
-- url     : https://prove2.me/theorems/5fc7cde1-5ff2-47b6-8b92-320b3d7cddab
-- title:
--   Lemma 3, (48), (49) — the interchange Lindbladian has gap at least $n$ on $P_n^\perp$
-- statement:
--   Let $\beta\ge0$ and $n\ge2$. The map $-\mathcal L_{IP}$ is KMS-self-adjoint with kernel $P_n$, and for every $X$,
--
--   $$\langle X,-\mathcal L_{IP}[X]\rangle_\rho=\frac12\sum_{i<j}\|X-\Delta_{e,(ij)}[X]\|_\rho^2 .$$
--
--   The KMS-orthogonal complement of $P_n$ coincides with the Hilbert–Schmidt one, $P_n^\perp$, which is invariant under $\mathcal L_{IP}$; every eigenvalue of $-\mathcal L_{IP}$ on it is at least $n$; equivalently $\langle X,-\mathcal L_{IP}[X]\rangle_\rho\ge n\|X\|_\rho^2$ for $X\in P_n^\perp$.
--
--   The bound comes from Aldous's spectral gap theorem on the complete graph, and it is what makes the bound on $P_n^\perp$ uniform in $n$.
--
--   Differences from the source:
--   - encoding: the Dirichlet form and the KMS norm, which are real for these generators → the real part of the complex inner product; reason: Lean's kmsInner is complex-valued
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Lemma 3, (48), (49), p.15 (PDF 16)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_KMS

open Matrix

namespace MFHeisGibbs

/-- **Lemma 3 (Spectral gap of the interchange Lindbladian)**, Raikovich, Mák, Czabán, Gilyén,
arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.15. `−L_IP` is KMS-self-adjoint with kernel `P_n`; (48); the KMS complement of `P_n` is the
Hilbert–Schmidt one, it is invariant under `L_IP`, every eigenvalue of `−L_IP` on it is at least `n`;
and (49). -/
theorem lemma_3 (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (hn : 2 ≤ n) :
    (∀ X Y : Op n, kmsInner β X (LIP n Y) = kmsInner β (LIP n X) Y) ∧
    (∀ X : Op n, LIP n X = 0 ↔ X ∈ Pn n) ∧
    (∀ X : Op n, dirichlet β (LIP n) X =
      (1 / 2) * ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        kmsNormSq β (X - swapOp i j * X * (swapOp i j)ᴴ)) ∧
    (∀ X : Op n, (∀ Y ∈ Pn n, kmsInner β Y X = 0) ↔ X ∈ hsPerp (Pn n)) ∧
    (∀ X ∈ hsPerp (Pn n), LIP n X ∈ hsPerp (Pn n)) ∧
    (∀ (l : ℂ) (X : Op n), X ∈ hsPerp (Pn n) → X ≠ 0 → -(LIP n X) = l • X →
      l.im = 0 ∧ (n : ℝ) ≤ l.re) ∧
    (∀ X ∈ hsPerp (Pn n), (n : ℝ) * kmsNormSq β X ≤ dirichlet β (LIP n) X) := by sorry

end MFHeisGibbs
