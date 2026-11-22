-- Prove2me | Theorems.Thm_GL2QFT_Circuits_qftGL2_eq_mackey_factorization
-- name    : GL2QFT.Circuits.qftGL2_eq_mackey_factorization
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T06:01:13.925169+00:00
-- url     : https://prove2.me/theorems/6836a83f-2672-4123-8d1a-63141344d859
-- title:
--   Exact 5-stage Mackey algebraic factorization and stage isometries for $F_{\mathrm{GL}_2(\mathbb{F}_q)}$
-- statement:
--   For every finite-field instance $D$, the $\mathrm{GL}_2(\mathbb{F}_q)$ quantum Fourier transform factors identically as
--
--   $$F_G = U_{\mathrm{reidx}} \cdot (I \otimes A_{\mathrm{tot}})\big|_{\mathrm{Mackey}} \cdot U_{N_{\mathrm{op}}} \cdot (I \otimes F_B) \cdot \mathrm{Enc}_{G/B},$$
--
--   with every intermediate stage an exact isometry ($M^\dagger M = I$), injective embeddings `mackeyMidEmb`, `mackeyOutEmb`, and vanishing of $I \otimes A_{\mathrm{tot}}$ outside `range (mackeyOutEmb D)` on inputs in `range (mackeyMidEmb D)`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Theorem 6.1, Lemma 3.5, Theorem 5.4 & §6.4.3 (pp. 17, 29–34, 44–47)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem qftGL2_eq_mackey_factorization (D : FieldData) : (D.qftGL2 = mackeyReindexMat D * Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) * mackeyNopMat D * frameMat (A := CosetT D) D.qftB * mackeyEncMat D) ∧ ((mackeyEncMat D).conjTranspose * mackeyEncMat D = 1) ∧ (D.qftB.conjTranspose * D.qftB = 1) ∧ ((mackeyNopMat D).conjTranspose * mackeyNopMat D = 1) ∧ ((totalA D).conjTranspose * totalA D = 1) ∧ (∀ m : MackeyMid D, ∀ y : (D.Lab × D.Lab) × OutReg D, (∀ m' : MackeyOut D, mackeyOutEmb D m' ≠ y) → frameMat (A := D.Lab × D.Lab) (totalA D) y (mackeyMidEmb D m) = 0) ∧ Function.Injective (mackeyMidEmb D) ∧ Function.Injective (mackeyOutEmb D) := by sorry

end Circuits
end GL2QFT
