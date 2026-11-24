-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_detM_b2
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_b2
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:11:37.593433+00:00
-- url     : https://prove2.me/theorems/717fa751-e347-4664-b16e-07eb67b89568
-- title:
--   Mod-1009 evaluation of `c_detM_WP` $dH/dQ$ component $b_1$
-- statement:
--   Verifies the explicit $\mathbb{F}_{1009}[U]/(P_{34})$ normal form of $b_1$ in `Poly1009.c_detM_WP`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L1185-L1205

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_b2 :
    let B : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 429, 199, 513, 792, 600, 635, 347, 337, 528, 568, 167, 415, 801, 885, 523, 3, 804, 798, 616, 46, 263], [0, 148, 851, 828, 316, 522, 347, 488, 259, 813, 676, 805, 819, 12, 908, 678, 484, 979, 934, 835, 725, 297, 486, 342])
    let Cc : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 84, 433, 932, 51, 490, 800, 352, 199, 218, 586, 1002, 172, 998, 920, 49, 547, 613, 987, 206, 500, 678], [0, 410, 989, 283, 772, 203, 720, 462, 192, 842, 234, 77, 313, 766, 989, 984, 711, 228, 928, 960, 349, 264, 794, 287])
    let xS : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 739, 371, 735, 197, 216, 711, 347, 456, 471, 808, 940, 318, 476, 9, 274, 0, 500, 895, 559, 223, 195], [0, 556, 955, 807, 889, 101, 277, 125, 95, 493, 478, 188, 782, 262, 81, 317, 423, 260, 411, 323, 464, 644, 891, 971])
    let xQ : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 125, 304, 231, 229, 488, 234, 330, 930, 32, 936, 153, 459, 1007, 353, 559, 617, 846, 989, 565, 261, 719], [0, 490, 730, 745, 736, 17, 425, 964, 290, 479, 349, 242, 880, 220, 445, 571, 722, 834, 132, 723, 449, 316, 961, 160])
    let ax : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 423, 470, 759, 178, 167, 687, 822, 848, 464, 679, 951, 525, 780, 577, 37, 17, 847, 909, 126, 782, 629], [0, 407, 756, 557, 11, 162, 106, 83, 960, 933, 476, 383, 549, 516, 864, 849, 421, 501, 700, 37, 309, 419, 425, 488])
    let bx : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 554, 503, 744, 12, 79, 869, 677, 258, 560, 495, 320, 874, 799, 229, 73, 620, 641, 778, 172, 307, 982], [0, 638, 572, 564, 43, 539, 772, 443, 549, 283, 16, 38, 690, 232, 344, 240, 197, 804, 57, 549, 165, 613, 438, 502])
    let b2 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([388, 547, 726, 876, 141, 665, 938, 146, 59, 895, 210, 685, 306, 997, 757, 757, 448, 564, 390, 278, 101, 652, 965, 208, 141, 325, 126, 268, 586, 393, 206, 107, 207, 396], [293, 897, 49, 166, 459, 517, 450, 253, 996, 150, 571, 210, 736, 995, 180, 58, 656, 710, 714, 64, 968, 466, 549, 1003, 939, 625, 182, 725, 46, 146, 412, 34, 526, 761])
    let b1_0 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([738, 82, 321, 952, 546, 30, 793, 765, 384, 374, 880, 73, 491, 694, 899, 708, 359, 211, 718, 249, 439, 339, 86, 79, 391, 325, 196, 983, 267, 158, 321, 952, 45, 584], [45, 312, 283, 545, 810, 448, 899, 614, 710, 584, 973, 347, 868, 564, 349, 185, 124, 660, 115, 411, 926, 341, 237, 322, 77, 27, 128, 730, 191, 365, 494, 312, 276, 21])
    let b1_x : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([750, 198, 482, 413, 144, 562, 966, 642, 302, 513, 635, 929, 591, 598, 667, 673, 781, 383, 65, 766, 157, 1003, 605, 773, 795, 453, 540, 981, 533, 131, 452, 359, 893, 547], [997, 201, 46, 422, 265, 56, 185, 517, 226, 129, 886, 10, 692, 364, 564, 982, 161, 892, 180, 387, 950, 598, 653, 492, 619, 551, 957, 571, 918, 331, 766, 715, 464, 670])
    let b1 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([154, 116, 803, 694, 845, 697, 275, 69, 651, 363, 124, 723, 381, 209, 5, 684, 623, 568, 818, 592, 169, 660, 966, 691, 841, 90, 133, 224, 138, 397, 415, 87, 840, 629], [44, 783, 15, 677, 206, 983, 247, 481, 461, 409, 631, 596, 970, 815, 209, 698, 826, 963, 718, 295, 587, 510, 418, 945, 450, 936, 367, 84, 479, 166, 404, 438, 545, 322])
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dQ_homP ax bx ([], []) = b1_0) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dQ_homP xS xQ ([], []) = b1_x) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qaddP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP b1_0 b2) b1_x) (SymmetricSexticResidual.CoverAlgebra.Poly1009.qscP [0, 10 * SymmetricSexticResidual.CoverAlgebra.Poly1009.params1009.inv7] (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmulP B Cc)) = b1) := by sorry
