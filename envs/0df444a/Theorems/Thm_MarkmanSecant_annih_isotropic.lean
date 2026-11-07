-- Prove2me | Theorems.Thm_MarkmanSecant_annih_isotropic
-- name    : MarkmanSecant.annih_isotropic
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T04:26:23.186072+00:00
-- url     : https://prove2.me/theorems/cb03277e-b3de-4a97-9666-d5f1baa75390
-- title:
--   The annihilator of a nonzero spinor is totally isotropic
-- statement:
--   Let $S=\bigwedge^*\mathbb C^{2n}$ be the spin representation and $V=\mathbb C^{2n}\oplus(\mathbb C^{2n})^*$ with the symmetric pairing $((w,t),(w',t'))=t(w')+t'(w)$. For any nonzero spinor $s$, its Clifford annihilator $\{v:m_v(s)=0\}$ is totally isotropic: the pairing vanishes on every pair of vectors in it. No purity or parity assumption is needed. This provides the isotropy required in the secant-similarity construction.
-- source:
--   Derived directly from the Clifford action in Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2, Section 2.1, equation (2.1.2). Proof uses the exterior-algebra square-zero relation and Mathlib CliffordAlgebra.contractLeft_ι_mul and contractLeft_contractLeft. https://arxiv.org/html/2502.03415v2

import Definitions.Def_MarkmanSecant

open MarkmanSecant

theorem MarkmanSecant.annih_isotropic (n : ℕ) (s : Spinor n) (hs : s ≠ 0)
    (v w : VC n) (hv : v ∈ annih s) (hw : w ∈ annih s) :
    pairV v w = 0 := by sorry
